import re
import sys
from enum import Enum
import random
import pyperclip

class AutoNumber(Enum):
    def __new__(cls):
        value = len(cls.__members__)  # note no + 1
        obj = object.__new__(cls)
        obj._value_ = value
        return obj

full_str = ""
def printc(str):
    global full_str
    full_str += (f"{str}\n")
    print(str)



regexes = ["^[a-zA-Z][0-9a-zA-Z]*$", "^[0-9][0-9]*$", "^if$", "^print$", "^else$", "^for$", "^while$", "^function$", "^continue$", "^break$",
           "^return$", "^=$", "^(\+|-)$", "^(\*|/|%)$", "^(==|!=)$", "^(<|>|<=|>=)$", "^\($", "^\)$", "^\{$", "^\}$", "^;$", "^~$", "^\*\*\*$"]

class Flag(Enum):
    CONTINUE = 0
    BREAK = 1
    RETURN = 2

class TType(AutoNumber):
    IDENT = ()
    NUMBER = ()
    IF = ()
    PRINT = ()
    ELSE = ()
    FOR = ()
    WHILE = ()
    FUNCTION = ()
    CONTINUE = ()
    BREAK = ()
    RETURN = ()
    EQUAL = ()
    BIN_OP_PLUS_MIN = ()
    BIN_OP_MULT_DIV = ()
    BIN_OP_EQ_NOTEQ = ()
    BIN_OP_GREATER_SMALLER = ()
    OPEN_BRACE = ()
    CLOSED_BRACE = ()
    OPEN_CURLY = ()
    CLOSED_CURLY = ()
    SEMICOLON = ()
    TILDE = ()
    THREE_STARS = ()

class REG_STAT(Enum):
    OCCUPIED = 0
    DIRTY = 1
    FREE = 2

class Var():
    def __init__(self, ident, reg=None):
        self.reg = reg
        self.stack = None
        self.ident = ident
        self.temp = False
        self.dirty = False
        self.evictible = True

def label_generator():
    num = 0
    while True:
        num_str = str(num)
        label = ""

        for digit in num_str:
            label += chr(97 + int(digit))

        num += 1
        yield label

def varname_generator():
    num = 0
    while True:
        num_str = str(num)
        label = "__"

        for digit in num_str:
            label += chr(97 + int(digit))

        num += 1
        yield label

class AR():
    def __init__(self, parent=None):
        self.mem = None
        self.parent = parent

        self.saved_vars = []

    def save_vars_on_stack(self):
        for var in self.mem.vars.values():
            # In saved vars we put all the vars that we need to restore to registers after the call
            # therefore only if the variable is in a register do we append it to the list for restoration
            if var.reg is not None:
                self.saved_vars.append(var)

                if var.stack is None or var.dirty:
                    self.mem.store_var_on_stack(var.ident)


    def invalidate_all_vars(self):
        # Invalidate it so that next time it's used it has to be picked up from the stack
        for var in self.mem.vars.values():
            if var.reg is not None:
                self.mem.register_varname[var.reg] = None
                self.mem.registers_status[var.reg] = REG_STAT.FREE
                var.reg = None

    def reload_saved_vals(self):
        for i in range(len(self.mem.registers_status)):
            self.mem.register_varname[i] = None
            self.mem.registers_status[i] = REG_STAT.FREE

        for var in self.saved_vars:
            printc(f"lw {self.mem.reg_name(var.reg)}, {var.stack}($fp)")
            self.mem.registers_status[var.reg] = REG_STAT.OCCUPIED
            self.mem.register_varname[var.reg] = var.ident

        self.saved_vars.clear()

    def init(self):
        printc(f"addi $sp, $sp, -8")
        printc(f"sw $ra, 4($sp)")
        printc(f"sw $fp, 0($sp)")
        printc(f"addi $fp, $sp, 4")

        self.mem = MemoryManager()

    def add_argument(self, name, arg_reg):
        offset_to_store = self.mem.init_var_on_stack(name)
        printc(f"sw ${self.mem.reg_name(arg_reg)}, {offset_to_store}($fp)")

    def destroy(self):
        printc(f"addi $sp, $fp, 4")
        printc(f"lw $ra, 0($fp)")
        printc(f"lw $fp, -4($fp)")


class MemoryManager():
    varname_gen = varname_generator()
    label_gen = label_generator()
    register_names = [f"$t{i}" for i in range(0, 10)] + [f"$s{i}" for i in range(0, 8)]

    def __init__(self, parent=None):
        self.parent = parent
        self.free_stack_offset = -4

        self.vars = {}
        self.registers_status = [REG_STAT.FREE for reg in MemoryManager.register_names]
        self.register_varname = [None for reg in MemoryManager.register_names]

    @staticmethod
    def create_new_mem(parent):
        new = MemoryManager(parent)

        new.vars = parent.vars.copy()
        new.registers_status = parent.registers_status
        new.register_varname = parent.register_varname

        return new

    @staticmethod
    def go_back_a_memory(mem_to_go_back_from):
        parent = mem_to_go_back_from.parent

        parent.registers_status = [REG_STAT.FREE for reg in MemoryManager.register_names]
        parent.register_varname = [None for reg in MemoryManager.register_names]

        for varobj in parent.vars.values():
            if varobj.reg is not None:
                parent.registers_status[varobj.reg] = REG_STAT.OCCUPIED
                parent.register_varname[varobj.reg] = varobj.ident

        return parent


    def init_new_var(self, ident, temp=False, evictible=True):
        reg_idx = self.get_free_register()
        self.vars[ident] = Var(ident, reg_idx)
        self.register_varname[reg_idx] = ident
        self.registers_status[reg_idx] = REG_STAT.OCCUPIED
        self.vars[ident].temp = temp
        self.vars[ident].evictible = evictible

        return reg_idx

    def init_new_var_on_stack(self, ident, temp=False):
        offset = self.move_stack_up()
        self.vars[ident] = Var(ident)
        self.vars[ident].temp = temp
        self.vars[ident].stack = offset

        return offset

    def delete_var(self, ident):
        if self.vars[ident].reg is not None:
            self.registers_status[self.vars[ident].reg] = REG_STAT.FREE
            self.register_varname[self.vars[ident].reg] = None

        del self.vars[ident]

    def change_varname(self, old_varname, new_varname, make_non_temp=False):
        reg = self.vars[old_varname].reg
        stack = self.vars[old_varname].stack
        del self.vars[old_varname]

        self.register_varname[reg] = new_varname
        self.vars[new_varname] = Var(new_varname, reg)
        self.vars[new_varname].stack = stack

        if make_non_temp:
            self.vars[new_varname].temp = False

    def make_non_evictible(self, varname):
        self.vars[varname].evictible = False

    def get_var_in_any_reg(self, varname):
        if varname not in self.vars:
            print(f"ERROR: Variable {varname} currently not accounted for!")
            exit()

        if self.vars[varname].reg is not None:
            return self.vars[varname].reg

        free_reg_idx = self.get_free_register()
        self.registers_status[free_reg_idx] = REG_STAT.OCCUPIED
        self.vars[varname].reg = free_reg_idx
        self.register_varname[free_reg_idx] = varname

        printc(f"lw {self.reg_name(free_reg_idx)}, {self.vars[varname].stack}($fp)")

        return free_reg_idx


    def get_free_register(self):
        for idx, reg_stat in enumerate(self.registers_status):
            if reg_stat == REG_STAT.FREE:
                return idx

        # No empty registers, we have to evict one
        rand_idx = random.randrange(0, len(MemoryManager.register_names))
        while not self.vars[self.register_varname[rand_idx]].evictible:
            rand_idx = random.randrange(0, len(MemoryManager.register_names))

        curr_var = self.register_varname[rand_idx]

        self.store_var_on_stack(curr_var)
        self.vars[curr_var].reg = None
        self.register_varname[rand_idx] = None

        return rand_idx

    def is_var_temp(self, ident):
        return self.vars[ident].temp

    def store_var_on_stack(self, varname):
        if self.vars[varname].stack is None:
            offset = self.move_stack_up()
            reg_idx = self.vars[varname].reg
            self.vars[varname].stack = offset
            printc(f"sw {MemoryManager.register_names[reg_idx]}, {self.vars[varname].stack}($fp)")

            self.vars[varname].dirty = False
        elif self.vars[varname].dirty:
            reg_idx = self.vars[varname].reg
            printc(f"sw {MemoryManager.register_names[reg_idx]}, {self.vars[varname].stack}($fp)")

            self.vars[varname].dirty = False

    def move_stack_up(self):
        printc(f"addi $sp, $sp, -4")
        self.free_stack_offset -= 4
        return self.free_stack_offset

    def reg_name(self, reg_idx):
        return MemoryManager.register_names[reg_idx]

    def get_rand_varname(self):
        return next(MemoryManager.varname_gen)

    def new_label(self):
        return next(MemoryManager.label_gen)

class ActivationRecord():
    def __init__(self, memorytree, parent):
        self.memory = memorytree
        self.parent = parent

class MemoryTree():
    def __init__(self, parent=None):
        self.parent_memory = parent
        self.mem = {}

    def __getitem__(self, key):
        if key not in self.mem:
            if self.parent_memory is not None:
                return self.parent_memory[key]
            else:
                print(f"ERROR: Uninitialized variable '{key}'")
                exit()

        return self.mem[key]

    def __setitem__(self, key, value):
        if key in self.mem:
            self.mem[key] = value
        else:
            if self.parent_memory is not None:
                if not self.parent_memory.set_var(key, value):
                    self.mem[key] = value

    def set_var(self, key, val):
        """THIS FUNCTION ONLY TO BE USED INTERNALLY"""
        if key in self.mem:
            self.mem[key] = val
            return True

        if self.parent_memory is not None:
            return self.parent_memory.set_var(key, val)

        return False

    def __delitem__(self, key):
        del self.mem[key]

class Node:
    def __init__(self):
        pass

    def exec(self, ar):
        pass

class Assignment(Node):
    def __init__(self, var, expr):
        super().__init__()
        self.var = var
        self.expr = expr

    def exec(self, ar):
        ident = self.var.identifier
        val = self.expr.exec(ar)

        ar.memory[ident] = val

        return None

    def compile(self, ar):
        mem = ar.mem

        ident = self.var.identifier
        res_name = self.expr.compile(ar)

        if ident not in mem.vars:
            # If we're initializing the new var now, we might as well just use change_varname
            mem.change_varname(res_name, ident, True)
        else:
            # But if we have it already, we must put the new value where the old one was
            if mem.vars[ident].reg is not None:
                printc(f"move {mem.reg_name(mem.vars[ident].reg)}, {mem.reg_name(mem.get_var_in_any_reg(res_name))}")

                if mem.vars[ident].stack is not None:
                    # This indicates that the value in the associated register might be different to the value in the associated stack offset
                    mem.vars[ident].dirty = True

            elif mem.vars[ident].stack is not None:
                printc(f"sw {mem.reg_name(mem.get_var_in_any_reg(res_name))}, {mem.vars[ident].stack}($fp)")
            else:
                print(f"ERROR: Variable '{ident}' exists, but isn't present either in register or in stack!")

        return None

class If_Statement(Node):
    def __init__(self, cond, block, else_block):
        super().__init__()
        self.condition = cond
        self.block = block
        self.else_block = else_block

    def exec(self, ar):
        condition = self.condition.exec(ar)
        if not isinstance(condition, bool):
            return None

        if condition:
            ret = self.block.exec(ar)
            if ret is not None:
                return ret
        else:
            if self.else_block != None:
                ret = self.else_block.exec(ar)
                if ret is not None:
                    return ret

        return None

    def compile(self, ar, end_function_lbl=None, loop_continue_lbls=None, loop_break_lbls=None):
        if loop_break_lbls is None:
            loop_break_lbls = []
        if loop_continue_lbls is None:
            loop_continue_lbls = []

        mem = ar.mem

        result_varname = self.condition.compile(ar)
        result_reg = mem.reg_name(mem.get_var_in_any_reg(result_varname))

        else_label = mem.new_label()
        printc(f"beqz {result_reg}, {else_label}")

        if mem.is_var_temp(result_varname):
            mem.delete_var(result_varname)

        self.block.compile(ar, end_function_lbl=end_function_lbl, loop_continue_lbls=loop_continue_lbls, loop_break_lbls=loop_break_lbls)

        if self.else_block == None:
            printc(f"{else_label}:")
        else:
            after_if_label = mem.new_label()
            printc(f"j {after_if_label}")
            printc(f"{else_label}:")
            self.else_block.compile(ar, end_function_lbl=end_function_lbl, loop_continue_lbls=loop_continue_lbls, loop_break_lbls=loop_break_lbls)
            printc(f"{after_if_label}:")

class Operator(Node):
    def __init__(self, left, op, right):
        super().__init__()
        self.left = left
        self.right = right
        self.op = op

    def exec(self, ar):
        if self.op == '+':
            return int(self.left.exec(ar)) + int(self.right.exec(ar))
        elif self.op == '-':
            return int(self.left.exec(ar)) - int(self.right.exec(ar))
        elif self.op == '==':
            return int(self.left.exec(ar)) == int(self.right.exec(ar))
        elif self.op == '!=':
            return int(self.left.exec(ar)) != int(self.right.exec(ar))
        elif self.op == '*':
            return int(self.left.exec(ar)) * int(self.right.exec(ar))
        elif self.op == '/':
            return int(self.left.exec(ar)) / int(self.right.exec(ar))
        elif self.op == '%':
            return int(self.left.exec(ar)) % int(self.right.exec(ar))
        elif self.op == '<':
            return int(self.left.exec(ar)) < int(self.right.exec(ar))
        elif self.op == '<=':
            return int(self.left.exec(ar)) <= int(self.right.exec(ar))
        elif self.op == '>':
            return int(self.left.exec(ar)) > int(self.right.exec(ar))
        elif self.op == '>=':
            return int(self.left.exec(ar)) >= int(self.right.exec(ar))
        else:
            print(f'ERROR: Invalid operator type: "{self.op}"')
            return False

    def compile(self, ar):
        mem = ar.mem

        left_varname = self.left.compile(ar)
        right_varname = self.right.compile(ar)
        type = self.op

        left = mem.reg_name(mem.get_var_in_any_reg(left_varname))
        right = mem.reg_name(mem.get_var_in_any_reg(right_varname))

        res_varname = mem.get_rand_varname()
        free_reg = mem.reg_name(mem.init_new_var(res_varname, temp=True))

        if type == "+":
            printc(f"add {free_reg}, {left}, {right}")
        elif type == '-':
            printc(f"sub {free_reg}, {left}, {right}")
        elif type == '*':
            printc(f"mul {free_reg}, {left}, {right}")
        elif type == '/':
            printc(f"div {free_reg}, {left}, {right}")
        elif type == '%':
            printc(f"div {left}, {right}")
            printc(f"mfhi {free_reg}")
        elif type == '==':
            printc(f"seq {free_reg}, {left}, {right}")
        elif type == '!=':
            printc(f"sne {free_reg}, {left}, {right}")
        elif self.op == '<':
            printc(f"slt {free_reg}, {left}, {right}")
        elif self.op == '<=':
            printc(f"sle {free_reg}, {left}, {right}")
        elif self.op == '>':
            printc(f"sgt {free_reg}, {left}, {right}")
        elif self.op == '>=':
            printc(f"sge {free_reg}, {left}, {right}")
        else:
            print(f"ERROR: Invalid operator {type}")

        if mem.is_var_temp(left_varname):
            mem.delete_var(left_varname)

        if mem.is_var_temp(right_varname):
            mem.delete_var(right_varname)

        return res_varname

class Variable(Node):
    def __init__(self, ident):
        super().__init__()
        self.identifier = ident

    def exec(self, ar):
        return ar.memory[self.identifier]

    def compile(self, ar):
        return self.identifier


class Number(Node):
    def __init__(self, num):
        super().__init__()
        self.num = int(num)

    def exec(self, ar):
        return self.num

    def compile(self, ar):
        mem = ar.mem

        varname = mem.get_rand_varname()
        reg = mem.reg_name(mem.init_new_var(varname, temp=True))
        printc(f"li {reg}, {self.num}")
        return varname

class Print(Node):
    def __init__(self, expr):
        super().__init__()
        self.expr = expr

    def exec(self, ar):
        res = self.expr.exec(ar)

        print(res)
        #if isinstance(res, str):
         #   print(res)
        #else:
         #   print("ERROR: ARGUMENT TO PRINT MUST BE A STRING!")

        return None

    def compile(self, ar):
        mem = ar.mem

        res_varname = self.expr.compile(ar)
        reg = mem.reg_name(mem.get_var_in_any_reg(res_varname))

        printc(f"li $v0, 1")
        printc(f"move $a0, {reg}")
        printc("syscall")

        if mem.is_var_temp(res_varname):
            mem.delete_var(res_varname)

class Program(Node):
    def __init__(self, funcs, block):
        super().__init__()
        self.funcs = funcs
        self.block = block

    def exec(self, ar):
        ret = self.block.exec(ar)

        if ret is not None:
            first_item = ret.pop(0)
            if first_item[0] == Flag.RETURN:
                print(f"ERROR: 'return' outside of function body")
            elif first_item[0] == Flag.CONTINUE:
                print(f"ERROR: 'continue' outside of loop")
            elif first_item[0] == Flag.BREAK:
                print(f"ERROR: 'break' outside of loop")

    def compile(self):
        printc(f"j main_program")
        printc("")
        printc("")
        printc("")

        for func in self.funcs:
            func.compile(None)
            printc("")

        printc("")

        printc(f"main_program:")
        ar = AR()
        ar.init()
        self.block.compile(ar)

        ar = ar.destroy()

        # end program
        printc("li $v0, 10")
        printc("syscall")

class Block(Node):
    def __init__(self, children):
        super().__init__()
        self.children = children

    def exec(self, ar, create_new_memory=True):
        if create_new_memory:
            new_mem = MemoryTree(ar.memory)
            ar.memory = new_mem

        for child in self.children:
            ret = child.exec(ar)

            if ret is not None:
                if create_new_memory:
                    ar.memory = ar.memory.parent_memory
                return ret


        # Return it back (i.e. discard variables that were created in the scope of the block that just ended)
        if create_new_memory:
            ar.memory = ar.memory.parent_memory

        return None

    def compile(self, ar, end_function_lbl=None, create_new_mem=True, loop_continue_lbls=None, loop_break_lbls=None):
        if loop_break_lbls is None:
            loop_break_lbls = []
        if loop_continue_lbls is None:
            loop_continue_lbls = []

        mem = ar.mem

        if create_new_mem:
            mem = MemoryManager.create_new_mem(mem)

        for child in self.children:
            if isinstance(child, Return):
                child.compile(ar, end_function_lbl=end_function_lbl)
            elif isinstance(child, If_Statement) or isinstance(child, While_Stat) or isinstance(child, For_Stat):
                child.compile(ar, end_function_lbl=end_function_lbl, loop_continue_lbls=loop_continue_lbls, loop_break_lbls=loop_break_lbls)
            elif isinstance(child, Break) or isinstance(child, Continue):
                child.compile(ar, loop_continue_lbls=loop_continue_lbls, loop_break_lbls=loop_break_lbls)
            else:
                child.compile(ar)

        if create_new_mem:
            # This will update mem accordingly
            mem = MemoryManager.go_back_a_memory(mem)

class Input(Node):
    def __init__(self):
        super().__init__()
        pass

    def exec(self, ar):
        return int(input())

    def compile(self, ar):
        mem = ar.mem

        printc("li $v0, 5")
        printc("syscall")

        varname = mem.get_rand_varname()
        free_reg = mem.reg_name(mem.init_new_var(varname, temp=True))

        printc(f"move {free_reg}, $v0")

        return varname

class For_Stat(Node):
    def __init__(self, lower, upper, internal_block, var_name, var_expr, start_is_lower, first_bound, second_bound):
        super().__init__()
        self.lower = lower
        self.upper = upper
        self.internal_block = internal_block
        self.var_name = var_name
        self.var_update = Assignment(Variable(var_name), var_expr)
        self.start_is_lower = start_is_lower
        self.first_bound = first_bound
        self.second_bound = second_bound


    def exec(self, ar):
        lower_val = self.lower.exec(ar)
        upper_val = self.upper.exec(ar)

        start_val = None
        if self.start_is_lower:
            start_val = lower_val if self.first_bound == "<=" else lower_val + 1
        else:
            start_val = upper_val if self.second_bound == "<=" else upper_val - 1

        new_mem = MemoryTree(ar.memory)
        ar.memory = new_mem

        ar.memory[self.var_name] = start_val

        first_check = lower_val < ar.memory[self.var_name] if self.first_bound == "<" else lower_val <= ar.memory[self.var_name]
        second_check = ar.memory[self.var_name] < upper_val if self.second_bound == "<" else ar.memory[self.var_name] <= upper_val
        while first_check and second_check:
            ret = self.internal_block.exec(ar, False)

            if ret is not None:
                first_flag = ret.pop(0)
                if first_flag[0] == Flag.CONTINUE:
                    pass
                elif first_flag[0] == Flag.BREAK:
                    ar.memory = ar.memory.parent_memory

                    if len(ret) > 0:
                        return ret
                    else:
                        return None
                else:
                    ar.memory = ar.memory.parent_memory
                    return ret


            # Update iteration variable
            self.var_update.exec(ar)

            first_check = lower_val < ar.memory[self.var_name] if self.first_bound == "<" else lower_val <= ar.memory[self.var_name]
            second_check = ar.memory[self.var_name] < upper_val if self.second_bound == "<" else ar.memory[self.var_name] <= upper_val


        ar.memory = ar.memory.parent_memory
        return None

    def compile(self, ar, end_function_lbl=None, loop_continue_lbls=None, loop_break_lbls=None):
        if loop_break_lbls is None:
            loop_break_lbls = []
        if loop_continue_lbls is None:
            loop_continue_lbls = []


        ar.mem = MemoryManager.create_new_mem(ar.mem)

        for_label = ar.mem.new_label()
        endfor_label = ar.mem.new_label()
        continue_label = ar.mem.new_label()

        loop_continue_lbls.append(continue_label)
        loop_break_lbls.append(endfor_label)

        command1 = "slt" if self.first_bound == "<" else "sle"
        command2 = "slt" if self.second_bound == "<" else "sle"

        lo_varname = self.lower.compile(ar)
        up_varname = self.upper.compile(ar)

        ar.mem.make_non_evictible(lo_varname)
        ar.mem.make_non_evictible(up_varname)

        lo = ar.mem.reg_name(ar.mem.get_var_in_any_reg(lo_varname))
        up = ar.mem.reg_name(ar.mem.get_var_in_any_reg(up_varname))

        iter_var = ar.mem.reg_name(ar.mem.init_new_var(self.var_name, evictible=False))
        if self.start_is_lower:
            if self.first_bound == "<":
                printc(f"addi {iter_var}, {lo}, 1")
            else:
                printc(f"move {iter_var}, {lo}")
        else:
            if self.second_bound == "<":
                printc(f"addi {iter_var}, {up}, -1")
            else:
                printc(f"move {iter_var}, {up}")

        printc(f"{for_label}:")

        res_varname = ar.mem.get_rand_varname()
        res = ar.mem.reg_name(ar.mem.init_new_var(res_varname, temp=True))
        printc(f"{command1} {res}, {lo}, {iter_var}")
        printc(f"beqz {res}, {endfor_label}")
        printc(f"{command2} {res}, {iter_var}, {up}")
        printc(f"beqz {res}, {endfor_label}")

        ar.mem.delete_var(res_varname)

        self.internal_block.compile(ar, create_new_mem=False, end_function_lbl=end_function_lbl, loop_continue_lbls=loop_continue_lbls, loop_break_lbls=loop_break_lbls)

        printc(f"{continue_label}:")

        # modify var - var modification now is integrated into self.internal_block
        self.var_update.compile(ar)


        printc(f"j {for_label}")

        printc(f"{endfor_label}:")

        ar.mem = MemoryManager.go_back_a_memory(ar.mem)
        # mem.delete_var(lo_varname)
        # mem.delete_var(up_varname)
        # mem.delete_var(self.var_name)
        # mem.delete_var(res_varname)

class While_Stat(Node):
    def __init__(self, cond, internal_block):
        super().__init__()
        self.cond = cond
        self.internal_block = internal_block

    def exec(self, ar):
        while self.cond.exec(ar) == True:
            ret = self.internal_block.exec(ar)

            if ret is not None:
                first_item = ret.pop(0)

                if first_item[0] == Flag.BREAK:
                    if len(ret) > 0:
                        return ret
                    else:
                        return None

        return None

    def compile(self, ar, end_function_lbl, loop_continue_lbls=None, loop_break_lbls=None):
        if loop_break_lbls is None:
            loop_break_lbls = []
        if loop_continue_lbls is None:
            loop_continue_lbls = []


        mem = ar.mem

        begin_lbl = mem.new_label()
        end_lbl = mem.new_label()

        loop_continue_lbls.append(begin_lbl)
        loop_break_lbls.append(end_lbl)

        printc(f"{begin_lbl}:")
        res_varname = self.cond.compile(ar)
        ar.mem.make_non_evictible(res_varname)

        reg = mem.reg_name(mem.get_var_in_any_reg(res_varname))

        printc(f"beqz {reg}, {end_lbl}")
        self.internal_block.compile(ar, end_function_lbl=end_function_lbl, loop_continue_lbls=loop_continue_lbls, loop_break_lbls=loop_break_lbls)
        printc(f"j {begin_lbl}")
        printc(f"{end_lbl}:")

        if mem.is_var_temp(res_varname):
            mem.delete_var(res_varname)


class Function(Node):
    def __init__(self, name, params, body):
        super().__init__()
        self.name = name
        self.params = params
        self.body = body
        self.func_lbl = None

    def exec(self, ar):
        pass

    def compile(self, ar):
        self.func_lbl = next(MemoryManager.label_gen)
        end_function_lbl = next(MemoryManager.label_gen)

        printc(f"{self.func_lbl}:")

        ar = AR(ar)
        ar.init()

        for idx, param in enumerate(self.params):
            ar.mem.vars[param.identifier] = Var(param.identifier)
            ar.mem.vars[param.identifier].stack = 4 + idx*4

        self.body.compile(ar, end_function_lbl=end_function_lbl)

        printc(f"{end_function_lbl}:")

        ar = ar.destroy()

        printc("jr $ra")


class Function_Call(Node):
    def __init__(self, name, args, func_node):
        super().__init__()
        self.name = name
        self.args = args
        self.func_node = func_node

    def exec(self, ar):
        if len(self.args) != len(self.func_node.params):
            print(f"FATAL ERROR: '{self.name}' requires {len(self.func_node.params)} parameters, but was given {len(self.args)}")
            exit()

        new_mem = MemoryTree()

        for arg_given, arg_taken in zip(self.args, self.func_node.params):
            new_mem.mem[arg_taken.identifier] = arg_given.exec(ar)

        new_ar = ActivationRecord(new_mem, ar)
        ret = self.func_node.body.exec(new_ar, False)

        del new_mem
        del new_ar

        if ret is None:
            return None

        if len(ret) > 1:
            print(f"ERROR: Invalid sequence of flags inside function call {[a[0] for a in ret]}")
            exit()

        first_item = ret.pop(0)

        if first_item[0] == Flag.RETURN:
            return first_item[1]
        elif first_item[0] == Flag.CONTINUE:
            print(f"ERROR: 'continue' outside of loop")
            exit()
        else:
            print(f"ERROR: 'break' outside of loop")
            exit()

    def compile(self, ar):
        if len(self.args) != len(self.func_node.params):
            print(f"FATAL ERROR: '{self.name}' requires {len(self.func_node.params)} parameters, but was given {len(self.args)}")
            exit()

        ar = AR(ar)
        ar.mem = ar.parent.mem

        #ar.save_vars_on_stack()

        arg_varnames = []

        for idx, arg in enumerate(self.args):
            arg_varname = arg.compile(ar)
            arg_varnames.append(arg_varname)

        # Should it be here? Most likely yes!
        ar.save_vars_on_stack()

        printc(f"addi $sp, $sp, {-4*len(self.args)}")
        for idx, arg in enumerate(self.args):
            printc(f"sw {ar.mem.reg_name(ar.mem.get_var_in_any_reg(arg_varnames[idx]))}, {4*idx}($sp)")


        printc(f"jal {self.func_node.func_lbl}")

        # Invalidate all variables because we don't know what will happen to the registers inside the function
        #ar.invalidate_all_vars()
        ar.reload_saved_vals()

        ar = ar.parent

        for arg_varname in arg_varnames:
            if ar.mem.is_var_temp(arg_varname):
                ar.mem.delete_var(arg_varname)

        # Remove arguments from the stack
        printc(f"addi $sp, $sp, {4*len(self.args)}")

        reg_varname = ar.mem.get_rand_varname()
        reg_idx = ar.mem.init_new_var(reg_varname, temp=True)
        printc(f"move {ar.mem.reg_name(reg_idx)}, $v0")

        return reg_varname



class Continue(Node):
    def __init__(self):
        super().__init__()

    def exec(self, ar):
        return [(Flag.CONTINUE,)]

    def compile(self, ar, loop_continue_lbls=None, loop_break_lbls=None):
        if loop_break_lbls is None:
            loop_break_lbls = []
        if loop_continue_lbls is None:
            loop_continue_lbls = []
        assert len(loop_continue_lbls) == len(loop_break_lbls)

        if len(loop_continue_lbls) == 0:
            print("ERROR: 'continue' outside of loop")
            exit()

        printc(f"j {loop_continue_lbls[-1]}")

class Break(Node):
    def __init__(self, lst):
        super().__init__()
        self.lst_to_ret = []
        self.num_breaks = 0
        self.continue_present = False

        for item in lst:
            if item.type == TType.BREAK:
                self.lst_to_ret.append((Flag.BREAK,))
                self.num_breaks += 1
            elif item.type == TType.CONTINUE:
                self.lst_to_ret.append((Flag.CONTINUE, ))
                self.continue_present = True
            else:
                print(f"ERROR: Invalid token in 'break' statement: '{item.val}'")

    def exec(self, ar):
        return self.lst_to_ret.copy()

    def compile(self, ar, loop_continue_lbls=None, loop_break_lbls=None):
        if loop_break_lbls is None:
            loop_break_lbls = []
        if loop_continue_lbls is None:
            loop_continue_lbls = []
        assert len(loop_continue_lbls) == len(loop_break_lbls)

        if len(loop_break_lbls) == 0:
            print("ERROR: 'break' outside of loop")

        if self.continue_present:
            if self.num_breaks + 1 > len(loop_continue_lbls):
                print(f"ERROR: Using {self.num_breaks} 'break' statements and one 'continue' when depth of loop nesting is {len(loop_continue_lbls)}")
                exit()

            printc(f"j {loop_continue_lbls[-self.num_breaks - 1]}")
        else:
            if self.num_breaks > len(loop_continue_lbls):
                print(f"ERROR: Using {self.num_breaks} 'break' statements when depth of loop nesting is {len(loop_continue_lbls)}")
                exit()

            printc(f"j {loop_break_lbls[-self.num_breaks]}")


class Return(Node):
    def __init__(self, to_ret):
        super().__init__()
        self.to_return = to_ret

    def exec(self, ar):
        return [(Flag.RETURN, self.to_return.exec(ar))]

    def compile(self, ar, end_function_lbl):
        res_varname = self.to_return.compile(ar)
        res_idx = ar.mem.get_var_in_any_reg(res_varname)

        printc(f"move $v0, {ar.mem.reg_name(res_idx)}")
        printc(f"j {end_function_lbl}")

class Token():
    def __init__(self, type, val):
        self.type = type
        self.val = val
# check out if300 - this is an identifier in C, so it's okay
# but if+ is def not an identifier and it actually is caught only after
# compiling so lexically it's okay, which is what i expected and how this
# lexical analysis built here works

class Lexer():
    def __init__(self, text):
        self.text = text
        self.generator = self.gen_tokens()
        self.next_token = []

    def eat(self, token_type):
        nxt = None
        if len(self.next_token) > 0:
            nxt = self.next_token.pop(0)
        else:
            nxt = next(self.generator)

        if nxt.type != token_type:
            print(f"ERROR: Invalid token '{nxt.val}', '{token_type}' expected!")
            exit()

        return nxt

    def eat_list(self, list_of_types):
        nxt = None
        if len(self.next_token) > 0:
            nxt = self.next_token.pop(0)
        else:
            nxt = next(self.generator)

        if nxt.type not in list_of_types:
            print(f"ERROR: Invalid token {nxt.val}")
            exit()

        return nxt

    def peek(self, num=1):
        if len(self.next_token) >= num:
            return self.next_token[num - 1]

        num_peeks = num - len(self.next_token)
        for i in range(0, num_peeks):
            self.next_token.append(next(self.generator))

        return self.next_token[-1]

    def gen_tokens(self):
        inp = self.text
        while len(inp) > 0:

            while inp[0] == " ":
                inp = inp[1:]

            last_success_idx = -1
            last_success_token = -1
            for a in range(0, len(inp)):
                substr = inp[:a + 1]
                at_least_one = False
                for index, regex in enumerate(regexes):
                    if re.search(regex, substr):
                        # printc(f"{index}, {regex}")
                        at_least_one = True
                        last_success_idx = a
                        last_success_token = index

                if not at_least_one and last_success_idx != -1:
                    break

            if last_success_token != -1:
                yield Token(TType(last_success_token), inp[:last_success_idx + 1])

                inp = inp[last_success_idx + 1:]
            else:
                print(f'ERROR: Invalid token "{inp}"')
                exit()

class Parser():
    def __init__(self, lexer):
        self.lex = lexer
        self.func_name_to_ast_node = {}

    def create_ast(self):
        return self.parse_program()

    def parse_program(self):
        funcs = []
        while self.lex.peek().type == TType.FUNCTION:
            funcs.append(self.parse_function_declaration())

        return Program(funcs, self.parse_block())

    def parse_function_declaration(self):
        self.lex.eat(TType.FUNCTION)

        ident = self.lex.eat(TType.IDENT).val
        self.lex.eat(TType.OPEN_BRACE)

        params = []
        if self.lex.peek().type != TType.CLOSED_BRACE:
            params.append(Variable(self.lex.eat(TType.IDENT).val))

        while self.lex.peek().type != TType.CLOSED_BRACE:
            self.lex.eat(TType.SEMICOLON)
            params.append(Variable(self.lex.eat(TType.IDENT).val))

        self.lex.eat(TType.CLOSED_BRACE)

        # This is done this way so that recursive calls in body can find where the name points to
        node = Function(ident, params, None)
        self.func_name_to_ast_node[ident] = node

        body = self.parse_block()
        node.body = body


        return node

    def parse_function_call(self):
        name = self.lex.eat(TType.IDENT).val
        self.lex.eat(TType.OPEN_BRACE)

        args = []
        if self.lex.peek().type != TType.CLOSED_BRACE:
            args.append(self.parse_expr1())

        while self.lex.peek().type != TType.CLOSED_BRACE:
            self.lex.eat(TType.SEMICOLON)
            args.append(self.parse_expr1())

        self.lex.eat(TType.CLOSED_BRACE)

        return Function_Call(name, args, self.func_name_to_ast_node[name])


    def parse_block(self):
        self.lex.eat(TType.OPEN_CURLY)

        children = []
        children.append(self.parse_statement())

        while self.lex.peek().type == TType.SEMICOLON:
            self.lex.eat(TType.SEMICOLON)
            children.append(self.parse_statement())

        self.lex.eat(TType.CLOSED_CURLY)

        return Block(children)

    def parse_statement(self):
        nxt = self.lex.peek()

        if nxt.type == TType.OPEN_CURLY:
            return self.parse_block()
        elif nxt.type == TType.IF:
            return self.parse_if_statement()
        elif nxt.type == TType.PRINT:
            return self.parse_print_statement()
        elif nxt.type == TType.TILDE:
            return self.parse_input()
        elif nxt.type == TType.FOR:
            return self.parse_for_statement()
        elif nxt.type == TType.WHILE:
            return self.parse_while_statement()
        elif nxt.type == TType.IDENT:
            if self.lex.peek(2).type == TType.OPEN_BRACE:
                return self.parse_function_call()
            else:
                return self.parse_assignment()
        elif nxt.type == TType.BREAK:
            return self.parse_break()
        elif nxt.type == TType.CONTINUE:
            return self.parse_continue()
        elif nxt.type == TType.RETURN:
            return self.parse_return()
        else:
            print(f"ERROR: Unexpected token {nxt.val}")
            exit()

    def parse_break(self):
        lst = []
        lst.append(self.lex.eat(TType.BREAK))

        while self.lex.peek().type == TType.BREAK:
            lst.append(self.lex.eat(TType.BREAK))

        if self.lex.peek().type == TType.CONTINUE:
            lst.append(self.lex.eat(TType.CONTINUE))

        if self.lex.peek().type == TType.BREAK:
            print(f"ERROR: Invalid 'break' after 'continue'")
            exit()

        return Break(lst)

    def parse_continue(self):
        self.lex.eat(TType.CONTINUE)
        return Continue()

    def parse_return(self):
        self.lex.eat(TType.RETURN)
        to_ret = self.parse_expr1()

        return Return(to_ret)

    def parse_if_statement(self):
        self.lex.eat(TType.IF)
        self.lex.eat(TType.OPEN_BRACE)

        cond = self.parse_expr()

        self.lex.eat(TType.CLOSED_BRACE)

        block = self.parse_block()

        else_block = None
        if self.lex.peek().type == TType.ELSE:
            self.lex.eat(TType.ELSE)
            else_block = self.parse_block()

        return If_Statement(cond, block, else_block)

    def parse_print_statement(self):
        self.lex.eat(TType.PRINT)
        self.lex.eat(TType.OPEN_BRACE)

        expr = self.parse_expr()

        self.lex.eat(TType.CLOSED_BRACE)

        return Print(expr)


    def parse_for_statement(self):
        start_is_lower = False

        self.lex.eat(TType.FOR)
        lower = self.parse_expr1()

        if self.lex.peek().type == TType.IDENT and self.lex.peek().val == 's':
            self.lex.eat(TType.IDENT)
            start_is_lower = True

        a = self.lex.eat(TType.BIN_OP_GREATER_SMALLER)
        if a.val not in ["<", "<="]:
            print(f"ERROR: Invalid syntax. Unexpected token {a.val}")
            exit()

        # var_name = self.lex.eat(TType.IDENT)
        # up_down = self.lex.eat(TType.BIN_OP_PLUS_MIN)

        # Im envisioning it to be something like for 0s <= a+50 <= 200 { block }
        # where s indicates the which of the bounds is the starting value

        var_name = self.lex.peek()
        var_expr = self.parse_expr1()

        b = self.lex.eat(TType.BIN_OP_GREATER_SMALLER)
        if b.val not in ["<", "<="]:
            print(f"ERROR: Invalid syntax. Unexpected token {b.val}")
            exit()

        upper = self.parse_expr1()

        if self.lex.peek().type == TType.IDENT and self.lex.peek().val == 's':
            if start_is_lower:
                print(f"ERROR: The modifier 's' must be included either on the lower or on the upper bound, but not both")
                exit()

            self.lex.eat(TType.IDENT)
        elif not start_is_lower:
            print(f"ERROR: For loop start bound not set. Please use 's' after one of the bound expressions to indicate that the for loop starts there")
            exit()

        internal_block = self.parse_block()

        return For_Stat(lower, upper, internal_block, var_name.val, var_expr, start_is_lower, a.val, b.val)

    def parse_while_statement(self):
        self.lex.eat(TType.WHILE)
        self.lex.eat(TType.OPEN_BRACE)
        cond = self.parse_expr()
        self.lex.eat(TType.CLOSED_BRACE)

        internal_block = self.parse_block()

        return While_Stat(cond, internal_block)


    def parse_assignment(self):
        ident = self.lex.eat(TType.IDENT).val
        self.lex.eat(TType.EQUAL)

        expr = self.parse_expr()

        return Assignment(Variable(ident), expr)

    def parse_expr(self):
        node = self.parse_expr1()

        while self.lex.peek().type in [TType.BIN_OP_EQ_NOTEQ, TType.BIN_OP_GREATER_SMALLER]:
            op = self.lex.eat_list([TType.BIN_OP_EQ_NOTEQ, TType.BIN_OP_GREATER_SMALLER]).val
            node = Operator(node, op, self.parse_expr1())

        return node

    def parse_expr1(self):
        node = self.parse_expr2()

        while self.lex.peek().type == TType.BIN_OP_PLUS_MIN:
            op = self.lex.eat(TType.BIN_OP_PLUS_MIN).val

            next_expr = self.parse_expr2()

            if isinstance(node, Number) and isinstance(next_expr, Number):
                node = Number(node.num + next_expr.num) if op == "+" else Number(node.num - next_expr.num)
            else:
                node = Operator(node, op, next_expr)

        return node

    def parse_expr2(self):
        node = self.parse_val()

        while self.lex.peek().type == TType.BIN_OP_MULT_DIV:
            op = self.lex.eat(TType.BIN_OP_MULT_DIV).val

            next_expr = self.parse_val()

            if isinstance(node, Number) and isinstance(next_expr, Number):
                if op == "*":
                    node = Number(node.num * next_expr.num)
                elif op == "/":
                    node = Number(node.num / next_expr.num)
                elif op == "%":
                    node = Number(node.num % next_expr.num)
            else:
                node = Operator(node, op, next_expr)

        return node

    def parse_val(self):
        nxt = self.lex.peek()

        node = None
        if nxt.type == TType.OPEN_BRACE:
            self.lex.eat(TType.OPEN_BRACE)
            node = self.parse_expr()
            self.lex.eat(TType.CLOSED_BRACE)
        if nxt.type == TType.IDENT:
            if self.lex.peek(2).type == TType.OPEN_BRACE:
                node = self.parse_function_call()
            else:
                ident_tok = self.lex.eat(TType.IDENT)
                node = Variable(ident_tok.val)
        elif nxt.type == TType.NUMBER:
            num = self.lex.eat(TType.NUMBER).val
            node = Number(num)
        elif nxt.type == TType.TILDE:
            node = self.parse_input()

        return node

    def parse_input(self):
        self.lex.eat(TType.TILDE)

        return Input()


def execute(tree_root):
    mem = MemoryTree()
    ar_main = ActivationRecord(mem, None)

    tree_root.exec(ar_main)

def compile(ast):
    ast.compile()
    pyperclip.copy(full_str)

if __name__ == "__main__":

    if len(sys.argv) > 1:
        with open(sys.argv[1], 'r') as file:
            inp = file.read().replace('\n', '')
    else:
        inp = input()

        if inp == "script":
            with open("script.ste", 'r') as file:
                inp = file.read().replace('\n', '')

    lexer = Lexer(inp)
    parser = Parser(lexer)

    ast = parser.create_ast()


    #execute(ast)
    compile(ast)