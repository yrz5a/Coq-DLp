A mechanization of the theory of dynamic logic DLp and its proof system in Coq. The version of Coq is 9.0.0. 

To run this file, use a Coq IDE (e.g. CoqIDE, VSCode/VSCoq on Windows) to open it. The Coq interpreter can directly run it and prove it. 

We adopt the approach of ``deep embedding'' of the logic, i.e., we represent the syntax of the logic as independent objects in Coq, not associating to objects in Prop. 
Our current version mainly focus on implementing a predicate transformer for the logic. 
In other words, we implement the proof system of DLp as extra axioms in Coq, without showing its correspondence to the semantics of the logic (which should be defined as other indepedent objects). 

