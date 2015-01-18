/* Chase Moran

In the input-reading code T stands for "Term", I.E, the entered forumla,
but for the rules section & prove, it always means "Tail" of the terms list.

AND right and OR left have branching, which is why they are not specified as rules

You'll see in the rules that it prints out which rule is used for each step.

In rules and prove, L and R are intended to stand for miscellaneous
terms on the left and right sides of the formula. They are lists of terms,
which works in the assumption that ands on the left and ors
on the right can be replaced with commas, though there is still an explicit
rule for this. (7 and 8.)

*/

% Infix operations
:- op(650, xfy, <=>).% Logically equivalent
:- op(600, xfy, =>). % x implies y
:- op(400, xfy, v ). % x or y
:- op(400, xfy, & ). % x and y
:- op(300, fy, ~ ).  % not y










/* The algorithm rules section

All rules of the algorithm, save AND right and OR left, which generate branching*/



/* Case where => appears on a side */
rule(L & [H => I|T] => R, L & [~H v I|T] => R, rule1).   % Left side

rule(L => R&[H => I|T], L => R & [~H v I|T], rule2).     % Right side


/* Case where <=> appears on a side */
rule(L & [H <=> I|T] => R, L & [(H => I)&(I => H)|T] => R, rule3). % Left

rule(L => R & [H <=> I|T], L => R & [(H => I) & (I => H)|T], rule8). % Right

/* Case where ~ is present */
rule(L & [~H|T] => R & R2, L & T => R & [H|R2], rule5). % left

rule(L1 & L2 => R & [~H|T], L1 & [H|L2] => R & T, rule6). % right

/* Case for & ON THE LEFT */
rule(L & [H& I|T] => R, L & [H,I|T] => R, rule7).

/* Case for v ON THE RIGHT */
rule(L => R & [H v I|T], L => R & [H,I|T], rule8).



/* Init takes input from the user and hands it off to the rest of the
program. Also quit as a term will satisfy it, so you can get out of the loop. */
init :-
    repeat,
    write('Please enter a formula.'),
    nl,
    read(T),
    (T==quit; handler(T), fail).
    
    
/* Handler is designed to 'handle' what prove is doing. It gets T from init
and then sees if T can be proven. If that fails, it prints that it can't be
proven. 
*/
handler(T) :-
    nl,
    nl,
    (prove([] & [] => [] & [T]),!, % Prove the entered term from nothing.
    nl,                           
    write('Formula is valid');  % Notice the OR
    nl,                            
    write('Formula is not valid')),
    nl,                            
    nl.

/* This is just a printing function, Though it makes the call back to prove. */
write_prove(T) :-
    write('prove,'),
    nl,
    write(T),
    nl,
    nl,
    prove(T).
    
    
/* Branching/ proving / most of the dirty work is handled by prove. */

/* Check if formula 1 satisfies a rule. If so, use that rule, and keep proving.
Also has printing */
prove(F1):-
    rule(F1,F2,Rule), !,
    write(F2),
    rule_used(Rule),
    nl,
    prove(F2).
    
    
/* Operating for OR on left side. 
If a formula matches with this rule, check
both branches created by the rule. */
prove(L & [H v I|T] => R) :-
    !,
    first_branch,
    write_prove(L & [H|T] => R),
    branch_success,
    second_branch,
    write_prove(L & [I|T] => R),
    branch_success.
    
    
/* Operating for & on right side. Other branching case. Same as above basically */
prove(L => R & [H & I|T]):-
    !,
    first_branch,
    write_prove(L => R&[H|T]),
    branch_success,
    second_branch,
    write_prove(L => R & [I|T]),
    branch_success.
    
/* Handles atomic cases. makes sure that whichever
of the two lists a term is is isn't a deciding factor. */
prove(L & [H|T] => R) :-
    !,
    prove([H|L]&T => R).

prove(L => R & [H|T]) :-
    !,
    prove(L => [H|R] & T).
    
    
    
/* Tautology verification. If T is a tautology, we're done. */
prove(T):-
    tautology(T),
    write('This is a tautology.'),
    nl.

/* Can't branch, doesn't meet a rule and isn't a tautology.
Catch anything and terminate. */
prove(_):-
    write('This branch has shown to be unprovable.'),
    fail.
    
    
    
/* Verify tautology. */
tautology(L & [] => R & []) :-
    member(X,L),
    member(X,R).
    
    
    
/* Printing formatting*/

branch_success :-
    write('This branch has succeeded'),
    nl.
    
first_branch :-
    nl,
    write('Evaluate first branch... ').
    
second_branch :-
    nl,
    write('Evaluate second branch... ').
    
rule_used(R):-
    write('    using '),
    write(R),
    nl,
    nl.
