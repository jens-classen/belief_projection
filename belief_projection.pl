/** <module> Projection of Extensional Belief

This file is a Prolog implementation of the projection methods and
examples for a Situation Calculus framework of an agent whose actions
are nondeterministic, and whose sensing is fallible, as described in
the paper

Jens Claßen and James P. Delgrande: Projection of Belief in the
 Presence of Nondeterministic Actions and Fallible Sensing. In
 Proceedings of the 19th International Conference on Principles of
 Knowledge Representation and Reasoning (KR 2022).

Although self-contained, this implementation is intended to be
compatible with the interpreter presented in the textbook

Raymond Reiter: Knowledge in Action - Logical Foundations for
Specifying and Implementing Dynamical Systems. MIT Press, 2001.

This program runs under SWI-Prolog (tested version: 8.3.8 for
x86_64-linux).

@author  Jens Claßen
@license GPLv2
*/

:- op(800, xfy, &).   % Conjunction 
:- op(850, xfy, v).   % Disjunction 
:- op(870, xfy, =>).  % Implication 
:- op(880, xfy, <=>). % Equivalence 

:- discontiguous b/3.
:- discontiguous acid/1.
:- discontiguous litmus/1.
:- discontiguous red/1.
:- discontiguous blue/1.

:- dynamic current/1.
:- dynamic b/3.
:- dynamic acid/1.
:- dynamic litmus/1.
:- dynamic red/1.
:- dynamic blue/1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory (domain-specific axioms)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% current situation
current(s0).

% initial values of B fluent
b(s1,0,s0).
b(s2,0,s0).
b(s3,1,s0).
b(s0,1,s0).

% values of physical fluents in initial situations
acid(s1).
litmus(s1).
litmus(s2).
acid(s3).

% situation-suppressed and -restored version of physical fluents
restoreSitArg(acid,S,acid(S)).
restoreSitArg(litmus,S,litmus(S)).
restoreSitArg(red,S,red(S)).
restoreSitArg(blue,S,blue(S)).

% successor state axioms for physical fluents
acid(do(_A,S)) :- acid(S).
litmus(do(_A,S)) :- litmus(S).
red(do(A,S)) :- (A = dip, acid(S), litmus(S)); red(S).
blue(do(A,S)) :- (A = dip, not(acid(S)), litmus(S)); blue(S).

% sensing fluent axioms
sf(sW(ok),S) :- not(red(S)), not(blue(S)).
sf(sW(ton),_S).

% intensional equivalence axioms
ieq(dip,dip).
ieq(sW(X),sW(Y)) :- member(X, [ok,ton,toff]), member(Y, [ok,ton,toff]).

% action plausibility axioms
apl(dip,0,_S).
apl(sW(ok),0,_S).
apl(sW(toff),1,_S).
apl(sW(ton),2,_S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Belief
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% successor state axiom for B fluent
b(SP,N,do(A,S)) :-
        b(SS,NS,S),
        apl(A,PP,S),
        ieq(A,AS),
        apl(AS,PS,SS),
        SP = do(AS,SS),
        agree(sf(AS,SS),sf(A,S)),
        N is NS + PP + PS.

% sensing fluent atoms F1 and F2 have the same truth value
agree(F1,F2) :- F1, F2.
agree(F1,F2) :- not(F1), not(F2).

% F is believed in S
bel(F,S) :-
        not((mp(SP,S), not(holds(F,SP)))).

% SP is a situation considered possible with minimal (im)plausibility at S
mp(SP,S) :-
        b(SP,P,S),
        not((b(_SPP,PP,S), P > PP)).

% belief state at situation S is given by B atoms in BS
bel_state(S,BS) :-
        findall(b(SP,P,S),b(SP,P,S),BS).

% phys. state at situation S is given by all true fluent atoms in PS
phy_state(S,PS) :-
        findall(F,phy_state_atom(S,F),PS).

% fluent atom F is true in a situation considered possible at S
phy_state_atom(S,F) :-
        b(SP,_,S),
        restoreSitArg(_,SP,F),
        F.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Regression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% check whether formula holds in situation S
% (revised Lloyd-Topor transformations)
holds(P & Q,S) :- !, holds(P,S), holds(Q,S).
holds(P v Q,S) :- !, holds(P,S); holds(Q,S).
holds(P => Q,S) :- !, holds(-P v Q,S).
holds(P <=> Q,S) :- !, holds((P => Q) & (Q => P),S).
holds(-(-P),S) :- !, holds(P,S).
holds(-(P & Q),S) :- !, holds(-P v -Q,S).
holds(-(P v Q),S) :- !, holds(-P & -Q,S).
holds(-(P => Q),S) :- !, holds(-(-P v Q),S).
holds(-(P <=> Q),S) :- !, holds(-((P => Q) & (Q => P)),S).
holds(-all(V,P),S) :- !, holds(some(V,-P),S).
holds(-some(V,P),S) :- !, not(holds(some(V,P),S)).
holds(-P,S) :- !, not(holds(P,S)).
holds(all(V,P),S) :- !, holds(-some(V,-P),S).
holds(some(V,P),S) :- !, subv(V,_,P,P1), holds(P1,S).
holds(A,S) :- restoreSitArg(A,S,F), !, F.
holds(A,_S) :- !, A.

% T2 is T1 with X1 substituted by X2
subv(X1,X2,T1,T2) :- var(T1), T1 == X1, !, T2 = X2.
subv(_,_,T1,T2)   :- var(T1), !, T2 = T1.
subv(X1,X2,T1,T2) :- T1 == X1, !, T2 = X2.
subv(X1,X2,T1,T2) :- T1 =..[F|L1], subvl(X1,X2,L1,L2), T2 =..[F|L2].
subvl(_,_,[],[]) :- !.
subvl(X1,X2,[T1|L1],[T2|L2]) :- !, subv(X1,X2,T1,T2), subvl(X1,X2,L1,L2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% progress current DB through action A
progress(A) :-
        retract(current(S)),
        bel_state(S,BScur),
        phy_state(S,PScur),
        bel_state(do(A,S),BSnew),
        phy_state(do(A,S),PSnew),
        forall(member(X1,BScur),retract(X1)),
        forall(member(Y1,PScur),retract(Y1)),
        forall(member(X2,BSnew),asserta(X2)),
        forall(member(Y2,PSnew),asserta(Y2)),
        assert(current(do(A,S))), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Helper Functions (Output)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% print a textual representation of belief state
print_bel_state(S) :-
        write('Belief state at '),
        write(S),
        write(':\n'),
        bel_state(S,BS),
        sort(2,@=<,BS,BSS),
        print_term(BSS,[]),
        write('\n').

% print a textual representation of physical state
print_phy_state(S) :-
        write('Physical state at '),
        write(S),
        write(':\n'),
        phy_state(S,PS),
        sort(PS,PSS),
        print_term(PSS,[]),
        write('\n').

% print a textual representation of physical and belief state at S
print_state(S) :-
        print_bel_state(S),
        print_phy_state(S).

% print a textual representation of current physical and belief state
print_current_state :-
        current(S),
        print_state(S).

% run (regression) query and print result
print_query_result(Q) :-
        Q, !,
        writef('%t: true\n', [Q]).
print_query_result(Q) :- !,
        writef('%t: false\n', [Q]).

% first situation argument is subhistory of second situation argument
subhistory(S1,do(_,S2)) :-
        subhistory(S1,S2).
subhistory(S,S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Run Examples
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

example_sequence(do(sW(ok),do(dip,s0))).
example_queries([litmus,acid,(-red)&(-blue)]).

regression_example(Sequence,Queries) :-
        forall(subhistory(S,Sequence),
               forall(member(F,Queries),
                      print_query_result(bel(F,S)))).

progression_example(s0) :-
        print_current_state.
progression_example(do(A,S)) :-
        progression_example(S),
        progress(A),
        print_current_state.

run :-
        example_sequence(Sequence),
        example_queries(Queries),
        
        writeln('\nRegression example:'),
        writeln('-------------------'),
        regression_example(Sequence,Queries),
        
        writeln('\nProgression example:'),
        writeln('--------------------'),
        progression_example(Sequence).
