# 2-CNF-Formula-Evaluator
This is a little program implementing the 2-CNF evaluation algorithm from "A linear-time algorithm for testing the truth of certain quantified boolean formulas" (Aspvall, Plass, Tarjan, 1979) after I came across the 2SAT problem in my Theory of Computation class at the FernUniversität in Hagen. 

More information can be found at https://en.wikipedia.org/wiki/2-satisfiability. 

No artificial intelligence tools were used to make the program.

<img width="807" height="724" alt="image" src="https://github.com/user-attachments/assets/3c571664-607e-4f1d-a07d-3c70bcad32ee" />

<img width="807" height="724" alt="image" src="https://github.com/user-attachments/assets/efd1623a-0a46-43b6-ace6-2ab2ef67a156" />

# Installation
The executable application was compiled by PyInstaller on Windows and therefore only runs on Windows. To run it: execute 2cnfeval.exe.

To run it on other operating systems: clone the repository, install the required packages 
```bash
pip install tkinter pillow networkx matplotlib
```
and execute 2cnfeval.py.

# How to use (and a little theory)
If you want details on how the algorithm works, you can read the 3-page paper "A linear-time algorithm for testing the truth of certain quantified boolean formulas" (Aspvall, Plass, Tarjan, 1979).

Input a 2-CNF formula in the white entry box at the top of the window and click the “Enter” button to the right of it. A string input is valid if it represents a 2-CNF formula with all quantifiers separated from the clauses, e.g. $`Q_1x_1Q_2x_2...Q_nx_n \ (x_i \vee x_j) \wedge \cdots \wedge (x_i \vee x_j), \ Q_k \in \{\exists, \forall\}`$ and makes the following symbol substitutions: $`\exists \to +, \ \forall \to \ ^*, \ \vee \to |, \ \wedge \to \&, \ \neg \to -`$. For example, the 2-CNF formula $`\forall a \exists b \ (a \vee \neg b) \wedge (\neg a \vee c)`$ is written as *a+b (a|-b) & (-a|c). Any variables that are not explicitly written with a quantifier are assumed to be existentially quantified. For simplicity, parentheses surrounding all clauses like ( (x|y) & ... & (x|y) ) are not allowed.

The program then evaluates the inputted formula using the algorithm from "A linear-time algorithm for testing the truth of certain quantified boolean formulas" (Aspvall, Plass, Tarjan, 1979) and displays the formula’s implication graph in the middle of the window as well as some information about the formula’s satisfiability at the bottom of the window.

For each variable $`x`$ there are two nodes $`x`$ and $`\neg x`$. For each clause $`(x \vee y)`$ there are two edges $`\neg x \to y, \ \neg y \to x`$. A node is coloured green / red / purple if the strongly connected component it belongs to is marked True / False / Contingent by the algorithm. A node is coloured grey if it did not have a marking before the algorihtm terminated prematurely. A node is a circle if the corresponding variable is existentially quantified, and a square if universally quantified. Edges are highlighted in the same colour as the nodes in a strongly connected component if there is more than one node in it.

If a formula is found to be satisfiable, the truth values of the variables are derived as follows: If a node belongs to a True or False strongly connected component, the corresponding literal gets assigned a value of True or False respectively. If it belongs to a Contingent strongly connected component, it inherits the truth value of the square node in the same component. In this implementation, it was decided to always assign the literal of the square node a value of True. The status bar at the bottom of the program will display such a mapping between variables and truth values. If a formula is not satisfiable, the status bar will display which unsatisfiability condition of the algorithm was tripped during evaluation.

The “Randomize formula” button randomly generates a 2-CNF formula and evaluates it on its satisfiability.
