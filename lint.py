import re
from datetime import datetime
from collections import defaultdict
import tkinter as tk
from tkinter import filedialog

class VerilogLinter:
    def __init__(self):
        self.errors = defaultdict(list)
        self.defined_registers = set()
        self.declarations = {}

    def parse_verilog(self, file_path):
        with open(file_path, 'r') as f:
            verilog_code = f.readlines()

        self.check_arithmetic_overflow(verilog_code)
        self.check_undefined_registers(verilog_code)
        self.check_multi_driven_registers(verilog_code)
        self.check_inferred_latches(verilog_code)
        self.check_full_or_parallel_case(verilog_code)
        self.check_duplicate_case_values(verilog_code)
        self.check_uninitialized_registers(verilog_code)
        self.check_incomplete_sensitivity_list(verilog_code)
        self.check_blocking_nonblocking_assignments(verilog_code)
        self.check_potential_race_conditions(verilog_code)
        self.check_array_index_out_of_bounds(verilog_code)

    # ---------------------------------------------------------------------------------------------------------------------------------------
    def check_arithmetic_overflow(self, verilog_code):
        variable_bits = {}
        overflow_pattern = r'\b(\w+)\s*=\s*(\w+)\s*([+\-*/])\s*(\w+)\b'

        for line in verilog_code:
            matches = re.findall(r'\b(input|output|reg|output\s*reg|wire)\s*(\[\d+:\d+\])?\s*(\w+)\b', line)
            for match in matches:
                variable_name = match[2]
                variable_bit = match[1]

                if variable_bit:
                    num1, num2 = map(int, re.findall(r'\d+', variable_bit))
                    variable_bits[variable_name] = abs(num1 - num2) + 1
                else:
                    variable_bits[variable_name] = 1  # Default 1-bit for undeclared widths

        for line_number, operation in enumerate(verilog_code, start=1):
            matches = re.findall(overflow_pattern, operation)
            for match in matches:
                signal = match[0]
                op1 = match[1]
                operator = match[2]
                op2 = match[3]

                def get_bitwidth(value):
                    return variable_bits.get(value, 1) if not value.isnumeric() else 1

                op1_bits = get_bitwidth(op1)
                op2_bits = get_bitwidth(op2)
                signal_bits = get_bitwidth(signal)

                if operator == '+' and signal_bits <= max(op1_bits, op2_bits):
                    self.errors['Arithmetic Overflow'].append(
                        (line_number, f"Signal '{signal}' may overflow as no enough bitwidth available.")
                    )
                elif operator == '-' and signal_bits < max(op1_bits, op2_bits):
                    self.errors['Arithmetic Overflow'].append(
                        (line_number, f"Signal '{signal}' may overflow. Bitwidth is not enough.")
                    )
                elif operator == '*':
                    if signal_bits < op1_bits + op2_bits:
                        self.errors['Arithmetic Overflow'].append(
                            (line_number, f"Signal '{signal}' may cause multiplication overflow.")
                        )
                elif operator == '/' and signal_bits < op1_bits:
                    self.errors['Arithmetic Overflow'].append(
                        (line_number, f"Signal '{signal}' may cause division overflow.")
                    )

    # ---------------------------------------------------------------------------------------------------------------------------------------
    def check_undefined_registers(self, verilog_code):
        declaration_pattern = r'\b(?:reg|wire|output)\s*([^;]+)\b'
        for line_number, line in enumerate(verilog_code,
                                           start=1):
            matches = re.findall(declaration_pattern, line)
            for match in matches:
                signal_names = re.findall(r'\b(\w+)\b', match)
                for signal in signal_names:
                    self.defined_registers.add(signal)

        usage_pattern = r'\b(\w+)\s*=\s*([^;]+)\b'
        for line_number, line in enumerate(verilog_code, start=1):
            matches = re.findall(usage_pattern, line)
            for match in matches:
                signal = match[0]

                if signal not in self.defined_registers:
                    self.errors['Undefined Register Usage'].append((line_number, f"Register '{signal}' is undefined "))

    # ---------------------------------------------------------------------------------------------------------------------------------------
    def check_multi_driven_registers(self, verilog_code):
        register_assignments = {}

        for line_number, line in enumerate(verilog_code, start=1):
            if re.search(r'\balways\s*@', line):
                always_block = self.extract_always_block(verilog_code, line_number)
                assignments = self.extract_register_assignments(always_block, line_number)

                for assignment in assignments:
                    register_name = assignment[0]
                    register_line_number = assignment[1]

                    if register_name not in register_assignments:
                        register_assignments[register_name] = register_line_number
                    else:
                        previous_line_number = register_assignments[register_name]
                        if previous_line_number != register_line_number:
                            self.errors['Multi-Driven Registers'].append(
                                (register_line_number,
                                 f"Register '{register_name}' is assigned in multiple always blocks. "
                                 f"Previous assignment at line {previous_line_number}.")
                            )
    def extract_always_block(self, verilog_code, line_number):
        always_block = []
        for line in verilog_code[line_number - 1:]:
            if re.search(r'\bend\b', line):
                always_block.append(line)
                break
            always_block.append(line)

        return ''.join(always_block)

    def extract_register_assignments(self, always_block, line_number):
        register_assignment_pattern = r'\b(\w+)\s*=\s*[^;]+\b'
        assignments = re.findall(register_assignment_pattern, always_block)
        return [(assignment, line_number + 1) for assignment in assignments]

    # ---------------------------------------------------------------------------------------------------------------------------------------

    def check_inferred_latches(self, verilog_code):
        verilog_code_str = ''.join(verilog_code)
        lines = verilog_code_str.splitlines()

        self.process_declarations(lines)

        for line_number, line in enumerate(lines, start=1):
            if re.search(r'\balways\s+@', line):
                always_block = self.extract_always_block(lines, line_number)
                if re.search(r'\bif\b', always_block):
                    if not self.has_else_branch(
                            always_block):
                        self.errors['Inferred Latches'].append(
                            (line_number, "Inferred latch found: 'if' statement without an 'else' branch."))

                if re.search(r'\bcase\b', always_block):
                    if not self.has_complete_cases(
                            always_block):

                        if not self.has_default_case(always_block):
                            self.errors['Inferred Latches'].append(
                                (line_number, "Inferred latch found: 'case' statement without a default case."))

    def process_declarations(self, lines):
        for line in lines:
            match = re.search(r'\breg\b\s*\[(\d+):(\d+)\]\s*(\w+)\s*;',
                              line)
            if match:
                start_bit = int(match.group(1))
                end_bit = int(match.group(2))
                name = match.group(3)
                size = start_bit - end_bit + 1
                self.declarations[name] = size
            if re.search(r'\bendmodule\b', line):
                break

    def has_else_branch(self, always_block):
        if_match = re.findall(r'\bif\s*\([^)]+\)', always_block)
        for if_statement in if_match:
            if re.search(r'else', if_statement):
                return True

        return False

    def has_default_case(self, always_block):
        case_match = re.search(r'\bcase\s*\([^)]+\)', always_block)
        if case_match:
            case_block = always_block[case_match.end():]
            return re.search(r'\bdefault\b', case_block)

        return True

    def has_complete_cases(self, always_block):
        case_match = re.search(r'\bcase\s*\(([^)]+)\)', always_block)
        if case_match:
            variable_name = case_match.group(1)
            case_block = always_block[case_match.end():]
            case_statements = re.findall(r'(\d+\'[bB][01]+)\s*:\s*', case_block, re.DOTALL)
            if case_statements:
                condition_bits = self.declarations.get(variable_name, 1)
                if len(case_statements) < (
                        2 ** condition_bits):
                    return False

        return True

    # ---------------------------------------------------------------------------------------------------------------------------------------
    def check_full_or_parallel_case(self, verilog_code):
        verilog_code_str = ''.join(verilog_code)
        lines = verilog_code_str.splitlines()

        self.process_declarations(lines)

        for line_number, line in enumerate(lines, start=1):
            if re.search(r'\balways\s+@', line):
                always_block = self.extract_always_block(lines, line_number)

                if re.search(r'\bcase\b', always_block):  # check the case statement
                    if not self.has_complete_cases(always_block):  # if it doesn't have complete cases
                        if not self.has_default_case(always_block):  # if it doesn't have default case
                            self.errors['Non Full Cases'].append(
                                (line_number, "Non Full Case Found: 'case' statement not full."))
                if re.search(r'\bcase\b', always_block):
                    if self.has_non_parallel_cases(always_block):  # if it doesn't have parallel case
                        self.errors['Non Parallel Cases'].append(
                            (line_number, "Non Parallel Case Found: 'case' statement not parallel."))

    def has_non_parallel_cases(self, always_block):
        case_match = re.search(r'\bcase\s*\(([^)]+)\)', always_block)
        if case_match:
            case_block = always_block[case_match.end():]
            case_statements = re.findall(r'(\d+\'[bB][01]+)\s*:\s*', case_block, re.DOTALL)
            has_duplicates = len(case_statements) != len(
                set(case_statements))
            if has_duplicates:
                return True

        return False
    #--------------------------------------------------------------------------------------------------------
    def check_duplicate_case_values(self, verilog_code):

        #case_pattern = r'^\s*case\s*\((.*?)\)\s*(.*?)\s*endcase'

        for line_number, line in enumerate(verilog_code, start=1):
            if re.search(r'^\s*case', line):
                case_block_start = line_number
                case_expr, case_block = self.extract_case_block(verilog_code, case_block_start)

                case_values = re.findall(r'(\d+\'[bB][01]+|\d+\'[hH][0-9A-Fa-f]+)', case_block)
                case_value_count = defaultdict(int)
                case_value_line_map = defaultdict(list)
                for value in case_values:
                    case_value_count[value] += 1
                    case_value_line_map[value].append(line_number)

                for value, count in case_value_count.items():
                    if count > 1:
                        duplicate_lines = case_value_line_map[value]
                        self.errors['Duplicate Case Values'].append(
                            (duplicate_lines[0],
                             f"Duplicate case value '{value}' found {count} times on lines {', '.join(map(str, duplicate_lines))} in case block starting at line {case_block_start}.")
                        )


    def extract_case_block(self, verilog_code, start_line):
        case_block = []
        case_expr = ''


        case_expr_match = re.search(r'^\s*case\s*\((.*?)\)', verilog_code[start_line - 1])
        if case_expr_match:
            case_expr = case_expr_match.group(1)

        for line_number in range(start_line, len(verilog_code)):
            line = verilog_code[line_number - 1]
            case_block.append(line)
            if 'endcase' in line:
                break

        return case_expr, ''.join(case_block)
    # ---------------------------------------------------------------------------------------------------------------------------------------
    def check_uninitialized_registers(self, verilog_code):
        initialized_regs = set()
        signal_usage = defaultdict(list)


        for line_number, line in enumerate(verilog_code, start=1):
            reg_name = self.reg_initialized(line)
            if reg_name:
                initialized_regs.add(reg_name)

            reg_usage = re.findall(r'(\w+)\s*=\s*([^;]+)', line)
            for assignment in reg_usage:
                variable = assignment[0]
                value = assignment[1]
                if value.isnumeric() and variable not in initialized_regs:
                    initialized_regs.add(variable)


        for line_number, line in enumerate(verilog_code, start=1):
            reg_usage = re.findall(r'=\s*([a-zA-Z_]\w*(?:\s*(?:[+\-*/]|and|or)\s*[a-zA-Z_]\w*)*)', line)
            for assignment in reg_usage:
                variables = re.findall(r'[a-zA-Z_]\w*', assignment)
                for variable in variables:
                    if variable not in initialized_regs:
                        signal_usage[variable].append(
                            line_number)

        for signal, lines in signal_usage.items():
            self.errors['Uninitialized Register Case'].append(
                (lines[0],
                 f"Uninitialized register '{signal}' used before initialization. Lines: {', '.join(map(str, lines))}."))
    def reg_initialized(self, line):
        match = re.search(r'reg\s+(?:\[\d+:\d+\])?\s*(\w+)\s*=',
                          line)
        if match:
            return match.group(1)
        return None

    # -------------------------------------------------------------------------------------------------------------

    def check_incomplete_sensitivity_list(self, verilog_code):
        warnings = []


        always_pattern = r'^\s*always\s*@\((.*?)\)\s*'
        end_pattern = r'\bend\b'

        total_lines = len(verilog_code)

        for line_number, line in enumerate(verilog_code, start=1):
            match = re.search(always_pattern, line)
            if match:
                sensitivity_list_raw = match.group(1)
                start_line = line_number

                if '*' in sensitivity_list_raw:
                    continue


                sensitivity_list = {s.strip() for s in re.split(r'[,\s]+', sensitivity_list_raw) if s.strip()}


                if 'clk' in sensitivity_list or 'rst' in sensitivity_list:
                    continue


                block_lines = []
                for block_line_number in range(line_number + 1, total_lines + 1):
                    block_line = verilog_code[block_line_number - 1]  # Adjust for zero indexing
                    block_lines.append(block_line)
                    if re.search(end_pattern, block_line):
                        break

                block = ''.join(block_lines)  # Join the block into a single string


                used_signals = set(re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\b', block))


                non_signals = {'if', 'else', 'begin', 'end', 'posedge', 'negedge', 'case', 'endcase', 'default'}
                used_signals -= non_signals


                missing_signals = used_signals - sensitivity_list


                if missing_signals:
                    warnings.append(
                        f"Line {start_line}: Incomplete sensitivity list: Missing signals {', '.join(missing_signals)} "
                        f"in block starting at line {start_line}."
                    )

        if warnings:
            self.errors['Incomplete Sensitivity List'] = warnings

    # ------------------------------------------------------------------------------------------------------------
    def check_blocking_nonblocking_assignments(self, verilog_code):
        warnings = []

        verilog_code_str = ''.join(verilog_code)

        always_pattern = r'always\s*@(.*?)\s*begin(.*?)\s*end'
        always_blocks = re.findall(always_pattern, verilog_code_str, re.DOTALL)

        for sensitivity, block in always_blocks:

            block_lines = block.splitlines()
            start_line_number = verilog_code_str.count('\n', 0, verilog_code_str.find(block)) + 1

            blocking_assignments = re.findall(r'(\w+)\s*=\s*[^;]+', block)
            non_blocking_assignments = re.findall(r'(\w+)\s*<=\s*[^;]+', block)
            is_clocked = 'posedge' in sensitivity or 'negedge' in sensitivity

            if is_clocked:
                for signal in blocking_assignments:
                    for idx, line in enumerate(block_lines):
                        if f"{signal} =" in line:
                            line_number = start_line_number + idx
                            warnings.append(
                                f"Line {line_number}: Blocking assignment ('=') to '{signal}' in clocked block. "
                                "Consider using non-blocking ('<=').")

            if not is_clocked:
                for signal in non_blocking_assignments:
                    for idx, line in enumerate(block_lines):
                        if f"{signal} <=" in line:
                            line_number = start_line_number + idx
                            warnings.append(
                                f"Line {line_number}: Non-blocking assignment ('<=') to '{signal}' outside clocked block. "
                                "Consider using blocking ('=').")

        if warnings:
            self.errors['Blocking assignment errors'] = warnings
    #----------------------------------------------------------------------------------------------------------------------
    def check_potential_race_conditions(self, verilog_code):
        always_pattern = r'always\s*@(.*?)\s*begin(.*?)\s*end'
        assign_pattern = r'assign\s+(\w+)\s*=\s*[^;]+;'

        verilog_code_str = ''.join(verilog_code)

        always_blocks = re.finditer(always_pattern, verilog_code_str, re.DOTALL)
        assigns = re.finditer(assign_pattern, verilog_code_str)

        signal_assignments = {}

        # Process always blocks
        for block_match in always_blocks:
            sensitivity, block = block_match.groups()
            block_start_char = block_match.start()
            block_start_line = verilog_code_str[:block_start_char].count('\n') + 1

            block_lines = block.split('\n')
            for i, line in enumerate(block_lines):
                line_number = block_start_line + i
                blocking_match = re.findall(r'(\w+)\s*=\s*[^;]+', line)
                non_blocking_match = re.findall(r'(\w+)\s*<=\s*[^;]+', line)

                for signal in blocking_match + non_blocking_match:
                    if signal not in signal_assignments:
                        signal_assignments[signal] = []
                    signal_assignments[signal].append(line_number)

        # Process assign statements
        for assign_match in assigns:
            signal = assign_match.group(1)
            assign_start_char = assign_match.start()
            line_number = verilog_code_str[:assign_start_char].count('\n') + 1

            if signal not in signal_assignments:
                signal_assignments[signal] = []
            signal_assignments[signal].append(line_number)

        # Check for race conditions
        for signal, lines in signal_assignments.items():
            if len(lines) > 1:
                self.errors['Race Condition'].append(
                    (lines, f"Signal '{signal}' assigned on lines {', '.join(map(str, lines))}"))
    #-----------------------------------------------------------------------------------------------------------------------
    def check_array_index_out_of_bounds(self, verilog_code):
        array_declarations = {}
        array_access_errors = []

        array_declaration_pattern = r'\b(reg|wire)\s*\[(\d+):(\d+)\]\s*(\w+)\s*\[(\d+):(\d+)\]\s*;'
        for line_number, line in enumerate(verilog_code, start=1):
            matches = re.findall(array_declaration_pattern, line)
            for match in matches:
                _, upper_data, lower_data, array_name, upper_index, lower_index = match
                upper_index, lower_index = int(upper_index), int(lower_index)
                array_size = abs(upper_index - lower_index) + 1
                array_declarations[array_name] = array_size

        array_access_pattern = r'(\w+)\[(\w+)\]'
        for line_number, line in enumerate(verilog_code, start=1):
            matches = re.findall(array_access_pattern, line)
            for array_name, index in matches:
                if array_name in array_declarations:
                    array_size = array_declarations[array_name]

                    if index.isdigit():
                        index_value = int(index)
                        if not (0 <= index_value < array_size):
                            array_access_errors.append(
                                (line_number,
                                 f"Array '{array_name}' index {index_value} out of bounds. Valid range: [0:{array_size - 1}].")
                            )
                    else:
                        array_access_errors.append(
                            (line_number,
                             f"Potential out of bounds access for array '{array_name}' with variable index '{index}'.")
                        )

        for error in array_access_errors:
            self.errors['Array Index Out of Bounds'].append(error)

    # ---------------------------------------------------------------------------------------------------------------------------------------
    def generate_report(self, report_file,file_name):
        with open(report_file, 'w') as f:
            timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            f.write(f"Lint Report for {file_name} generated at: {timestamp}\n\n")

            for violation, lines in self.errors.items():
                f.write(f"{violation}:\n")
                for line in lines:
                    if isinstance(line, tuple) and len(line) == 2:
                        line_number, message = line
                        f.write(f"\tLine {line_number}: {message}\n")
                    else:
                        f.write(f"\tInvalid entry in lines: {line}\n")
"""
linter = VerilogLinter()
root = tk.Tk()
root.withdraw()
file_name = filedialog.askopenfilename(
    title="Select a Verilog file to lint",
    filetypes=(("Verilog files", "*.v"), ("All files", "*.*"))
)
if file_name:
    linter.parse_verilog(file_name)
    linter.generate_report('lint_report.txt', file_name)
    print(f"Linting completed. Report generated as 'lint_report.txt'.")
else:
    print("No file selected.")
"""
linter = VerilogLinter()
file_name = "Test cases/"
linter.parse_verilog(file_name)
linter.generate_report('lint_report.txt',file_name)
