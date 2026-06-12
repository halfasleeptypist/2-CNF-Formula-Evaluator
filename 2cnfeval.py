from tkinter import * # for GUI
from tkinter import ttk
from tkinter import messagebox
from PIL import ImageTk, Image # for displaying image in GUI
import networkx as nx # for graph data structure
import matplotlib.pyplot as plt # for displaying graph in plot
import re # for pattern matching of inputted formula
import random # for randomize_formula method

# Raised when inputted formula doesn't represent a 2-CNF formula.
class InvalidFormulaError(Exception):
    def __init__(self, formula: str):
        print(f"Inputted {formula = } is invalid!")
        # raise Exception("Inputted formula is invalid!")

# Raised when one of the unsatisfiability conditions in the evaluation algorithm is met.
class FormulaNotSatisfiableError(Exception):
    def __init__(self, result: str):
        print(f"Formula is not satisfiable! {result}")
        # raise Exception("Formula is not satisfiable!")

# Encapsulates the 2-CNF evaluator algorithm including private helper functions, and holds data variables for later access.
class TwoCNFEvaluator:
    def __init__(self):
        self.formula: str = "" # holds inputted formula
        self.variables: dict[str, dict[str, int|str|bool]] = {} # dict of variables with index of appearance in formula (int), corresponding quantifier (str) and truth value (bool)
        self.impl_graph: nx.DiGraph = nx.DiGraph() # implication graph of formula
        self.result: str = "" # str for describing interpretation that satisfies or unsatisfiability condition that was met during evaluation
    
    # Returns the complement of a literal. Is x or its negation -x the given literal, so is __compl(x) = -x or __compl(-x) = x, respectively.
    def __compl(self, lit: str) -> str:
        if lit.startswith("-"):
            return lit.removeprefix("-")
        else:
            return "-" + lit
    
    # Returns the atom of a given literal. Is x or its negation -x the given literal, so is __absolute(x) = x or __absolute(-x) = x, respectively.
    def __absolute(self, lit: str) -> str:
        return lit.removeprefix("-")

    # Generates a random formula in 2-CNF to evaluates it on its satisfiability.
    # The formula contains 2-6 variables and 1-10 clauses.
    def randomize_formula(self):
        number_of_vars: int = random.randint(2, 6)
        number_of_clauses: int = random.randint(1, 10)
        f: str = ""
        for i in range(number_of_vars):
            q: str = random.choice(["+", "*"])
            f = f + q + "x" + str(i+1)
        f = f + " "
        cl: list[str] = []
        used_cl: list[tuple[int, int]] = []
        for i in range(number_of_clauses):
            j1: int = random.randint(1, number_of_vars)
            j2: int = random.choice([x for x in range(1, number_of_vars+1) if x != j1])
            if sorted((j1, j2)) not in used_cl:
                used_cl.append(sorted((j1, j2)))
                n1: str = random.choice(["-", ""])
                n2: str = random.choice(["-", ""])
                cl.append(f'({n1}x{j1}|{n2}x{j2})')
        f += " & ".join(cl)
        self.evaluate(f)
        
    # Evaluates a given 2-CNF formula on its satisfiability using an implementation of the 2-CNF evaluation algorithm from
    # "A linear-time algorithm for testing the truth of certain quantified boolean formulas" (Aspvall, Plass, Tarjan, 1979).
    # The formula, its variables, its implication graph and the algorithm's result after evaluation are stored for later display in GUI.
    def evaluate(self, formula: str):
        # Initialize variables and erase data from previous formula before evaluation.
        self.formula = formula
        self.variables = {}
        self.impl_graph = nx.DiGraph()
        self.result = ""
        node_attrs: dict[str, dict[str, str]] = {} # holds node attributes for later colouring and shaping in displayed graph
        #edge_attrs: dict = {}
        
        # (1) Parse string input and check that it represents a valid formula in 2-CNF 
        # with any amount of quantified variables. If string input doesn't fit those patterns, raise error.
        # User input represents a 2-CNF formula if the following symbol substitutions are made: ∃ -> +, ∀ -> *, ∨ -> |, ∧ -> &, ¬ -> -.
        # All clauses (x|y) must be enclosed in parentheses and have & symbols between them.
        # For simplicity, parentheses surrounding all clauses like ( (x|y) & ... & (x|y) ) are not allowed.
        f: str = formula.replace(" ", "") # remove whitespace
        if re.fullmatch(r"([\+|\*]\w+)*(\(-?\w+\|-?\w+\)\&)*\(-?\w+\|-?\w+\)", f) is None:
            raise InvalidFormulaError(self.formula)
        
        # (2a) Store any quantified variables found in formula and create corresponding vertices in implication graph.
        f_quant: str = f[:f.index("(")] # is empty string if formula has no quantifiers
        #print(f"{f_quant = }")
        if f_quant != "":
            f_quant_var: list[str] = [x for x in re.split(r'[\+\*]', f_quant) if x != ""] # returns list of variables
            f_quant_q: list[str] = [x for x in re.split(r'\w+', f_quant) if x != ""] # returns list of quantifiers
            self.variables = {var: {"index": i, "quantifier": f_quant_q[i]} for i, var in enumerate(f_quant_var)}
            self.impl_graph.add_nodes_from(list(self.variables.keys()) + [self.__compl(var) for var in self.variables.keys()])
            node_attrs |= {var: {"color": "tab:gray", "shape": "s"} if f_quant_q[i] == "*" else {"color": "tab:gray", "shape": "o"} for i, var in enumerate(f_quant_var)}
            node_attrs |= {self.__compl(var): {"color": "tab:gray", "shape": "s"} if f_quant_q[i] == "*" else {"color": "tab:gray", "shape": "o"} for i, var in enumerate(f_quant_var)}
            #print(f"{f_quant_var = }, {f_quant_q = }")
            #print(f"{self.variables = }")
    
        # (2b) Store any variables found in a clause of formula and create corresponding vertices and edges in implication graph.
        # If a variable has not been explicitly quantified before, assume it's existentially quantified and placed after all already quantified variables.
        f_cnf: str = f[f.index("("):]
        #print(f"{f_cnf = }")
        clauses: list[str] = f_cnf.split("&")
        for clause in clauses:
            literals: list[str] = [x for x in re.split(r'[\(\|\)]', clause) if x != ""]
            for l in literals:
                if self.__absolute(l) not in self.variables:
                    self.variables[self.__absolute(l)] = {"index": len(self.variables), "quantifier": "+"}
                    self.impl_graph.add_nodes_from([l, self.__compl(l)])
                    node_attrs[l] = {"color": "tab:gray", "shape": "o"}
                    node_attrs[self.__compl(l)] = {"color": "tab:gray", "shape": "o"}
            u: str = literals[0]
            v: str = literals[1]
            self.impl_graph.add_edge(self.__compl(u), v)
            self.impl_graph.add_edge(self.__compl(v), u)
        #edge_attrs = {edge: {"color": "tab:gray"} for edge in self.impl_graph.edges()}
        #print(f"{self.variables = }")

        #print(f"{node_attrs = }")
        #print(f"{edge_attrs = }")
        nx.set_node_attributes(self.impl_graph, node_attrs) # integrate node attributes into graph for later parsing and displaying
        #nx.set_edge_attributes(self.impl_graph, edge_attrs)
        #print(self.impl_graph.nodes.data())
        #print(self.impl_graph.edges.data())
        
        # (3) Compute strongly connected components (strong comps) of the implication graph.
        # Its condensation H is also computed to determine if a strong comp is a successor or a predecessor of another.
        H: nx.DiGraph[int] = nx.condensation(self.impl_graph)
        strong_comp_members = H.nodes.data() # type NodeView[int, dict[str, set[str]]]
        node_to_strong_comp: dict[str, int] = H.graph["mapping"] # dict mapping a node to index of strongly connected comp of G it belongs in
    
        # (4) 2-CNF evaluation algorithm goes through strong comps in reverse topological order.
        # If the algorithm prematurely ends because an unsatisfiability condition is met, store description of the condition in the result variable.
        strong_comp_marks: dict[int, str] = {} # maps node in H to marking
        strong_comp_universal_vert: dict[int, str] = {} # maps strong comp to one universal vert (if it has any)
        for s in list(reversed(list(nx.topological_sort(H)))):
            verts_in_s: set[str] = strong_comp_members[s]["members"] # set of nodes
            step: int = 1
            
            # Step 1: If S is marked, go on to the next component.
            # Otherwise if some successor of S is marked false or contingent, go to Step 2.
            # Otherwise go to Step 3.
            if step == 1:
                if s in strong_comp_marks:
                    continue
                step = 3
                for succ in H.successors(s):
                    if strong_comp_marks[succ] == "false" or strong_comp_marks[succ] == "contingent":
                        step = 2
                        break
    
            # Step 2: S has a false or contingent successor.
            # If S contains one or more universal vertices, stop.
            # Otherwise, mark S false and go to Step 5.
            if step == 2:
                for vert in verts_in_s:
                    if self.variables[self.__absolute(vert)]["quantifier"] == "*":
                        self.result = f"The strongly connected component of vertex {vert} contains one or more universal vertices while having a false or contingent successor."
                        nx.set_node_attributes(self.impl_graph, node_attrs)
                        raise FormulaNotSatisfiableError(self.result)
                strong_comp_marks[s] = "false"
                node_attrs |= {vert: {"color": "tab:red"} for vert in verts_in_s}
                step = 5
    
            # Step 3: All successors of S are true.
            # If S contains two or more universal vertices, stop.
            # Otherwise, if S contains one universal vertex u_i, go to Step 4.
            # Otherwise, mark S true and go to Step 5.
            if step == 3:
                number_universal_verts: int = 0
                for vert in verts_in_s:
                    if self.variables[self.__absolute(vert)]["quantifier"] == "*":
                        number_universal_verts += 1
                        strong_comp_universal_vert[s] = vert
                if number_universal_verts >= 2:
                    self.result = f"The strongly connected component of vertex {strong_comp_universal_vert[s]} contains more than one universal vertex while all of its successors are true."
                    nx.set_node_attributes(self.impl_graph, node_attrs)
                    raise FormulaNotSatisfiableError(self.result)
                elif number_universal_verts == 1:
                    step = 4
                else:
                    strong_comp_marks[s] = "true"
                    node_attrs |= {vert: {"color": "tab:green"} for vert in verts_in_s}
                    step = 5
    
            # Step 4: S contains a universal vertex u_i.
            # If S contains an existential vertex u_j with j < i, stop.
            # Otherwise, mark S contingent and go to Step 5.
            if step == 4:
                for vert in verts_in_s:
                    if self.variables[self.__absolute(vert)]["quantifier"] == "+" and self.variables[self.__absolute(vert)]["index"] < self.variables[self.__absolute(strong_comp_universal_vert[s])]["index"]:
                        self.result = f"The strongly connected component containing the universal vertex {strong_comp_universal_vert[s]} contains an existential vertex {vert} that is quantified earlier in the formula."
                        nx.set_node_attributes(self.impl_graph, node_attrs)
                        raise FormulaNotSatisfiableError(self.result)
                strong_comp_marks[s] = "contingent+"
                node_attrs |= {vert: {"color": "tab:purple"} for vert in verts_in_s}
                step = 5
    
            # Step 5: S is marked successfully.
            # If S equals dual comp of S, stop.
            # Otherwise, go to Step 6.
            # The dual comp of a strong comp S is the strong comp in which the complements of the vertices of S are part of.
            if step == 5:
                for vert in verts_in_s: # check for only one vert
                    if node_to_strong_comp[self.__compl(vert)] != s: # if vert and compl(vert) are not in same strong comp
                        comp_equals_dual = False
                        step = 6
                        break
                    else:
                        self.result = f"The strongly connected component containing vertex {vert} is equal to its dual component."
                        nx.set_node_attributes(self.impl_graph, node_attrs)
                        raise FormulaNotSatisfiableError(self.result)
    
            # Step 6: S is not equal to dual comp of S.
            # If S is marked contingent or false and dual comp of S precedes S, stop.
            # Otherwise mark dual comp of S false if S is true,
            # contingent if S is contingent, and true if S is false.
            # Go on to the next component.
            if step == 6:
                if strong_comp_marks[s] == "contingent+" or strong_comp_marks[s] == "false":
                    for vert in verts_in_s:
                        if node_to_strong_comp[self.__compl(vert)] in H.predecessors(s):
                            self.result = f"The strongly connected component containing vertex {vert} is marked contigent and false, and its dual component precedes it."
                            nx.set_node_attributes(self.impl_graph, node_attrs)
                            raise FormulaNotSatisfiableError(self.result)
                        break
                vert: str = verts_in_s.copy().pop()
                if strong_comp_marks[s] == "true":
                    strong_comp_marks[node_to_strong_comp[self.__compl(vert)]] = "false"
                    node_attrs |= {self.__compl(vert): {"color": "tab:red"} for vert in verts_in_s}
                if strong_comp_marks[s] == "contingent+":
                    strong_comp_marks[node_to_strong_comp[self.__compl(vert)]] = "contingent-"
                    node_attrs |= {self.__compl(vert): {"color": "tab:purple"} for vert in verts_in_s}
                if strong_comp_marks[s] == "false":
                    strong_comp_marks[node_to_strong_comp[self.__compl(vert)]] = "true"
                    node_attrs |= {self.__compl(vert): {"color": "tab:green"} for vert in verts_in_s}
            
        nx.set_node_attributes(self.impl_graph, node_attrs) # integrate node attributes into graph for later parsing and displaying
        #print(f"{node_attrs = }")
        
        # (5) Assign truth values to variables.
        # The corresponding variable to a vertex in a true or false strong comp gets assigned True or False, respectively.
        # Only the true strong comps are processed because the false strong comps are exactly the dual comps of the true strong comps,
        # and so assigning truth values to the variables of the vertices in false strong comps would be the same process except with complementary truth values.
        true_comps: list[int] = [s for s in strong_comp_marks if strong_comp_marks[s] == "true"]
        for s in true_comps:
            verts_in_s: set[str] = strong_comp_members[s]["members"] # set of nodes
            for vert in verts_in_s:
                if vert.startswith("-"):
                    self.variables[self.__compl(vert)]["truth"] = False
                else:
                    self.variables[vert]["truth"] = True
        # For the same reason as above, we only look at comps marked with "contingent+".
        # Each vertex in a contingent component containing the universal vertex u_i gets
        # assigned the truth value of x_i if u_i = x_i and the complementary truth value
        # if u_i = -x_i. There is a choice to be made whether all vertices are to be assigned
        # True or False respectively in the former case and False or True respectively in the latter case.
        # This implements the former case.
        contingent_comps: list[int] = [s for s in strong_comp_marks if strong_comp_marks[s] == "contingent+"]
        for s in contingent_comps:
            verts_in_s: set[str] = strong_comp_members[s]["members"] # set of nodes
            universal_vert: str = strong_comp_universal_vert[s]
            if universal_vert.startswith("-"): # assign all verts false
                for vert in verts_in_s:
                    if vert.startswith("-"):
                        self.variables[self.__compl(vert)]["truth"] = True
                    else:
                        self.variables[vert]["truth"] = False
            else:
                for vert in verts_in_s: # assign all verts true
                    if vert.startswith("-"):
                        self.variables[self.__compl(vert)]["truth"] = False
                    else:
                        self.variables[vert]["truth"] = True

        # for console
        satis = [(data["index"], var, data["truth"]) for var, data in self.variables.items()]
        print(f"Formula {formula} is satisfiable for {sorted(satis, key=lambda tup: tup[0])}!")

        # Save variables and their truth values.
        self.result = ", ".join([f"{entry[1]} = {entry[2]}" for entry in sorted(satis, key=lambda tup: tup[0])])

# Called when user clicks on "Randomize formula" button.
# After evaluation of a randomly generated 2-CNF formula, it displays the formula and the implication graph.
# If the formula is satisfiable, display an appropriate interpretation in the status bar.
# Otherwise, display the unsatisfiability condition that was met during evaluation.
def randomize():
    try:
        #print(f"{str(root.winfo_width()) = }, {str(root.winfo_height()) = }")
        evaluator.randomize_formula()
        result.set(f"F is satisfiable for: {evaluator.result}!")
    except FormulaNotSatisfiableError:
        result.set(f"F is not satisfiable! {evaluator.result}")
    finally:
        formula.set(evaluator.formula)
        render_graph(evaluator.impl_graph)

# Called when user clicks on "Enter" button after inputting a formula.
# If inputted formula is not in 2-CNF, display an error message to the user.
# After evaluation of the inputted 2-CNF formula, it displays the implication graph.
# If the formula is satisfiable, display an appropriate interpretation in the status bar.
# Otherwise, display the unsatisfiability condition that was met during evaluation.
def press_enter():
    text = formula.get()
    if text != "" and not text.isspace():
        try:
            evaluator.evaluate(text)
            result.set(f"F is satisfiable for: {evaluator.result}!")
            render_graph(evaluator.impl_graph)
        except InvalidFormulaError: 
            messagebox.showerror(message='Formula is invalid! Please type in a formula in 2-CNF!')
        except FormulaNotSatisfiableError:
            result.set(f"F is not satisfiable! {evaluator.result}")
            render_graph(evaluator.impl_graph)

# Renders the implication graph of a 2-CNF formula after it has been evaluated on satisfiability.
# A node corresponding to a variable is circular if it is existentially quantified, or square if universally quantified.
# A node is green/red/purple if the corresponding variable has been marked as true/false/contingent by the evaluation algorithm.
# If the graph contains strongly connected components of more than one node, the edges are highlighted in the nodes' colour.
# The nodes are arranged in a circular pattern to prevent node overlap (but not edge overlap).
def render_graph(G: nx.DiGraph):
    plt.clf() # clears graph view for a new graph to be inserted later
    pos = nx.forceatlas2_layout(G)
    pos = nx.kamada_kawai_layout(G, pos) # using one of these layouts on their own causes node overlaps, so apply both of them to create circular layout
    #print(pos)
    for node, data in G.nodes.data():
        nx.draw_networkx_nodes(G, pos, nodelist=[node], node_shape=data["shape"], node_color=data["color"], node_size=300)
        for nbr in G.successors(node):
            if nx.has_path(G, nbr, node):
                nx.draw_networkx_edges(G, pos, edgelist=[(node, nbr)], edge_color=data["color"], width=5.0, alpha=0.6) 
    nx.draw_networkx_edges(G, pos, arrows=True, alpha=0.5)
    nx.draw_networkx_labels(G, pos, font_size=10, font_color="whitesmoke")
    plt.savefig("graph.png")
    imgobj = ImageTk.PhotoImage(Image.open("graph.png"))
    graph_view.configure(image=imgobj)
    graph_view.image = imgobj


# Creates instance of TwoCNFEvaluator to then pass inputted formula to.
evaluator = TwoCNFEvaluator()

# Creates window.
root = Tk()
root.title("2-CNF Evaluation")

# Creates bits and pieces of GUI.
content = ttk.Frame(root)
topleft = ttk.Label(content, text="F =", anchor="center")
formula = StringVar()
formula_input = ttk.Entry(content, textvariable=formula)
enter = ttk.Button(content, text="Enter", command=press_enter)
randomize = ttk.Button(content, text="Randomize formula", command=randomize)
imgobj = ImageTk.PhotoImage(Image.open("start_placeholder.png"))
graph_view = ttk.Label(content, image=imgobj)
graph_view.image = imgobj
result = StringVar()
result_label = ttk.Entry(content, textvariable=result, state=["readonly"])
s_result = ttk.Scrollbar(content, orient=HORIZONTAL, command=result_label.xview)
result_label["xscrollcommand"] = s_result.set

# root.bind('<Return>', lambda e: enter.invoke())

# Arranges bits and pieces of GUI.
content.grid(column=0, row=0, sticky="nwes")
topleft.grid(column=0, row=0, sticky="nwes")
formula_input.grid(column=1, row=0, sticky="nwes")
enter.grid(column=2, row=0, sticky="nwes")
randomize.grid(column=3, row=0, sticky="nwes")
#frame.grid(column=0, row=1, columnspan=4, sticky="nwes")
#graph_view.grid(column=0, row=0, sticky="nwes")
graph_view.grid(column=0, row=1, columnspan=4, sticky="nwes")
result_label.grid(column=0, row=2, columnspan=4, sticky="nwes")
s_result.grid(column=0, row=3, columnspan=4, sticky="nwes")

# Scales rows and columns appropriately and disables resizing.
root.columnconfigure(0, weight=1)
root.rowconfigure(0, weight=1)
#content.columnconfigure(0, weight=1)
content.columnconfigure(1, weight=1)
#content.columnconfigure(2, weight=3)
#content.columnconfigure(3, weight=3)
#content.rowconfigure(0, weight=1)
content.rowconfigure(1, weight=1)
#content.rowconfigure(2, weight=1)
#frame.columnconfigure(0, weight=1)
#frame.rowconfigure(0, weight=1)
root.resizable(False, False)

# starts the program
root.mainloop()