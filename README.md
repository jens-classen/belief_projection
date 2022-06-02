# Belief Projection

This repository is a prototype implementation of the projection
methods and examples for a Situation Calculus framework of an agent
whose actions are nondeterministic, and whose sensing is fallible, as
described in the paper

> Jens Claßen and James P. Delgrande: Projection of Belief in the
> Presence of Nondeterministic Actions and Fallible Sensing. In
> Proceedings of the 19th International Conference on Principles of
> Knowledge Representation and Reasoning (KR 2022).

Although self-contained, this implementation is intended to be
compatible with the [interpreter][1] presented in the [textbook][2]

Raymond Reiter: Knowledge in Action - Logical Foundations for
Specifying and Implementing Dynamical Systems. MIT Press, 2001.

[1]: http://www.cs.toronto.edu/cogrobo/kia/
[2]: https://mitpress.mit.edu/books/knowledge-action

This program runs under SWI-Prolog (tested version: 8.3.8 for
x86_64-linux).

To run the program, simply call the goal

    ?- run.

and observe the output for the regression and progression examples.
