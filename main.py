"""FSA to RegExp translator"""
import sys
import re

class FSAInputParser:
    """ A class for parsing inputs from file to further processing.
    """
    class Container:
        """
            Auxiliary class for parsing input.
        """
        def __init__(self):
            self.st = None

    def __init__(self, file):
        self.input_file = file
        self.states = None
        self.alpha = None
        self.initial = FSAInputParser.Container()
        self.accepting = FSAInputParser.Container()
        self.trans = None

    def parse_input(self):
        """
        Parses the input from file.
        """
        with open(self.input_file, "r") as in_file:
            for i in range(5):
                line = in_file.readline()
                if len(line) == 0:
                    raise FSAValidator.FSAValidationError("E0: Input file is malformed ")
                self.execute_line(line)

    def execute_line(self, line: str):
        """
        Here we use a trick to avoid extra parsing of input.
        The input has structure similar with Python lists, excluding identifiers that are unknown to Python.
        However, if we wrap the contents of "lists" using quotes, we can execute the input line as
        a regular Python statement assigning a list reference.

        In general this approach is quite dangerous since the malicious party can execute arbitrary code in such a way,
        however, in this paritucular case fits our task quite well.
        """
        try:
            identif = re.search(r'.+?=', line).group(0)  # get identifier
            elements = re.search(r'\[(.*)]', line).group(1)  # get arguments in brackets
            if len(elements) == 0:
                elements = []
            else:
                elements = re.split(r',', elements)  # split arguments by comma
            statement = f'self.{identif}{str(elements)}'  # string representation of list looks like regular Python list
            exec(statement)  # assign variables
            if len(self.states) <= 0:
                raise AttributeError()
        except AttributeError as e:
            raise FSAValidator.FSAValidationError("E0: Input file is malformed")

    def get_parameters(self):
        """ Return extracted parameters of FSA. """
        return (self.states,
                self.alpha,
                self.initial,
                self.accepting,
                self.trans)


class FSARepresentation:
    """ A representation of FSA with all states and transitions. """

    class Transition:
        """ A class for storing transitions. """

        def __init__(self, _prev, _str, _next):
            self.prev_state = _prev
            self.string = _str
            self.next_state = _next

    class State:
        """ A class for storing states. """

        def __init__(self, name: str):
            self.name = name
            self.transitions = dict()  # key - string, value = new state name
            self.deterministic = True
            self.leads_here = []

    def __init__(self, params):
        """
        Parameters:
        params -- set of FSA characteristics, should be obtained using FSAInputParser """
        self.states, self.alpha, self.initial, self.accepting, self.trans = params
        self.states_map = dict()
        self.transitions = []

    def fill_transitions(self):
        """ Create internal transitions list. """
        for t in self.trans:
            _prev, _string, _next = t.split(">")
            self.transitions.append(FSARepresentation.Transition(_prev, _string, _next))

    def build_fsa_model(self):
        """
            Create model of FSA that we will use for validation.
            states_map will store State instances accessible by name.
            Each State instance contains all its transitions.
        """
        # fill the states_map with declared states (that also will help to find E1 non-declared states)
        state_ref = None
        for state_name in self.states:
            self.states_map[state_name] = FSARepresentation.State(name=state_name)
        try:
            for tr in self.transitions:
                # fill the previous state (name and transition)
                key = tr.prev_state
                state_ref = self.states_map[key]  # get state
                if tr.string in state_ref.transitions:  # got string already present in transitions map
                    state_ref.deterministic = False  # different transitions for same string
                state_ref.transitions[tr.string] = tr.next_state  # put mapping in the dict

                # fill the next state (which states lead there)
                key = tr.next_state
                state_ref = self.states_map[key]  # get state
                state_ref.leads_here.append(tr.prev_state)
        except KeyError as e:
            raise FSAValidator.FSAValidationError(f'E1: A state {str(e)} is not in the set of states')

    def to_regexp(self) -> str:
        """
            Converts inner FSA representation to a regexp string using Kleene's algorithm.
        :return:    regexp string
        """
        # auxiliary function for temporary regexp sets R^{k} storage
        def empty_matrix(size: int, contents=""):
            m = []
            for i in range(size):
                m.append([])
                for j in range(size):
                    m[i].append(contents)
            return m
        fsa = self
        states_len = len(fsa.states)
        R = empty_matrix(states_len)
        k = -1
        # fill for regexps with k = -1
        for i in range(states_len):
            for j in range(states_len):
                flag = False #  flag to put empty set if no transitions are found
                R_set = []
                # if there exists a transition from q_i to q_j
                if fsa.states[i] in fsa.states_map[fsa.states[j]].leads_here:
                    flag = True
                    for tr in fsa.transitions:
                        if tr.prev_state == fsa.states[i] and tr.next_state == fsa.states[j]:
                            R_set.append(tr.string)
                if i == j:
                    R_set.append("eps")
                    flag = True
                if not flag:
                    R_set.append("{}")
                regexp = R_set[0]
                for r in range(1, len(R_set)):
                    regexp += "|" + R_set[r] # append all found regexps as a union
                R[i][j] = regexp

        # next we will iteratively use R^k (R_next) and R^{k-1}  to obtain regexps
        R_next = empty_matrix(states_len)
        for it in range(states_len):
            k += 1
            for i in range(states_len):
                for j in range(states_len):
                    R_next[i][j] = "(" + R[i][k] + ")" + "(" + R[k][k] + ")*" + "(" + R[k][j] + ")" + "|" + "(" + R[i][j] + ")"
            R = R_next
            R_next = empty_matrix(states_len)

        ans = ""
        for i in range(states_len):
            if fsa.states[i] in fsa.accepting:
                ans += R[0][i] + "|"
        if len(fsa.accepting) == 0:
            ans = "{} "
        return ans[0:-1]


class FSAValidator:
    """ Provides main validation functionality for FSAs described using FSARepresentation. """

    def __init__(self):
        self.visited_map = dict()
        input_parser = FSAInputParser("input.txt")
        input_parser.parse_input()

        fsa_parameters = input_parser.get_parameters()
        self.fsa = FSARepresentation(fsa_parameters)
        self.fsa.fill_transitions()
        self.fsa.build_fsa_model()

    def getFSA(self) -> FSARepresentation:
        return self.fsa

    class FSAValidationError(Exception):
        """ Exception on validation errors. """

        def __init__(self, message=""):
            self.message = message

    class FSAValidationWarning(Exception):
        """ Exception on validation warnings. """

        def __init__(self, message=""):
            self.message = message

    def validate_E2(self):
        """
            Validates E2: Some states are disjoint
        """
        self.find_disjoints()

    def find_disjoints(self):
        """
            Finds a disjoint state, i.e. such that both
            can't be reached and leads to no other state except itself
        :return:
        """
        for string, state in self.fsa.states_map.items():
            # filter what states lead to that state excluding itself
            leads_here_without_itself = filter(lambda x: x != state.name, state.leads_here)
            leads_here_without_itself = list(leads_here_without_itself)
            # assign flag
            leads_here_only_itself = len(leads_here_without_itself) == 0

            is_initial_state = state.name in self.fsa.initial
            transition_only_to_itself = True
            # Try to find other transitions
            for letter, state_name in state.transitions.items():
                if state_name != state.name:
                    transition_only_to_itself = False
                    break
            # resulting test for disjointness
            if leads_here_only_itself and (not is_initial_state) and transition_only_to_itself:
                raise FSAValidator.FSAValidationError("E2: Some states are disjoint")

    def validate_E3(self):
        """
            Validates E3: a transition is not represented in the alphabet
        """
        for tr in self.fsa.transitions:
            self.is_in_alphabet(tr.string)

    def is_in_alphabet(self, _string: str):
        """
            Checks if a letter belongs to FSA alphabet
        :param _string: string to be checked
        :return: True if a letter belongs to FSA alphabet; False otherwise
        """
        if _string not in self.fsa.alpha:
            raise FSAValidator.FSAValidationError(f"E3: A transition '{_string}' is not represented in the alphabet")

    def validate_E4(self):
        """
            Validates FSA for error E4: Initial state is not defined
        """
        if len(self.fsa.initial) == 0:
            raise FSAValidator.FSAValidationError("E4: Initial state is not defined")
        self.fsa.states_map[self.fsa.initial[0]]

    def visit(self, state: FSARepresentation.State):
        """
        # find disjoint states by performing a DFS from the initial state
        :param state: current visiting state
        """
        self.visited_map[state.name] = True
        for string, state_name in state.transitions.items():
            if not self.visited_map[state_name]:
                self.visit(self.fsa.states_map[state_name])

    def validate_E5(self):
        """
            Validates FSA for error E5: FSA is nondeterministic
        """
        for name, state in self.fsa.states_map.items():
            if not state.deterministic:
                raise FSAValidator.FSAValidationError("E5: FSA is nondeterministic")

    def is_complete(self) -> bool:
        """
            Checks completeness of every state, i.e. if every state has transitions for every letter of the alphabet.
        :return: True if every state is complete; False otherwise.
        """
        for name, state in self.fsa.states_map.items():
            if not self._is_complete(state):
                return False
        return True

    def _is_complete(self, state: FSARepresentation.State) -> bool:
        """
            Checks completeness of particular state.
        :param: state: examined state.
        :return: True if the state is complete; False otherwise.
        """
        for a in self.fsa.alpha:
            if not (a in state.transitions):
                return False
        return True

    @staticmethod
    def exception_wrapper(func, f, warning_print) -> bool:
        """
        A wrapper for handling exceptions on validation warnings
        :param func: function to be run
        :param f: file stream
        :param warning_print: print "Warning:" or not
        :return: warning_print: True if it was not printed, False otherwise.
        """
        try:
            func()
        except FSAValidator.FSAValidationWarning as e:
            if warning_print:
                warning_print = False
                f.write("Warning:\n")
            f.write(e.message + '\n')
        return warning_print

    @staticmethod
    def run():
        """
            Primary method for validating FSA and converting it to regexp
        """
        error_print = True
        with open("output.txt", "w") as f:
            try:
                try:
                    val = FSAValidator()
                    val.validate_E2()
                    val.validate_E3()
                    val.validate_E4()
                    val.validate_E5()
                    f.write(val.getFSA().to_regexp())
                except KeyError as ex:
                    raise FSAValidator.FSAValidationError(f'E1: A state {str(ex)} is not in the set of states')
            except FSAValidator.FSAValidationError as e:
                if error_print:
                    f.write("Error:\n")
                f.write(e.message)
                f.write('\n')
                return


def main():
    """ Boilerplate code """
    FSAValidator.run()

if __name__ == '__main__':
    sys.exit(main())
