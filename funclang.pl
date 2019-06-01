/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    funclang prolog -- a prolog interpretor for simple funclang.
	
	Serveral necessary adjustments are made because of some restrictions of the prolog languege
	Different from the java console we developed, every query in the prolog console will be an independent run,
	which means the environment can not be preserved between one and another run.
	The original define expression dose not make sense because every query is a new run.
	So I took the strategy similar to Lisp when defining function. Just use (definefunc Name Varables FuncBody)(Body)
	Put the function call in the body part. 
	Also, user can define variables with (define var val) during function defination, see the test cases for more examples
	
	Prolog can be make executable but no one is actually doing that. Things start to get platform specific quickly and 
	prolog is not recommending doing that: http://www.swi-prolog.org/FAQ/MakeExecutable.html
	
	Also the libaries for that has not been updated for years, it is not working on my computer.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- set_prolog_flag(double_quotes, chars). %set double_quotes means chars

parsing(String, Exprs) :- phrase(expressions(Exprs), String). %parsing the string input to the expressions

%ws is a space or just empty set
ws --> [W], { char_type(W, space) }, ws.
ws --> [].

/*expressions is: space expression space followed by the rest of expressions  
empty set is also an expression for empty string
*/
expressions([E|Es]) -->
    ws, expression(E), ws,
    !, % cut opertor to find the single matching output
    expressions(Es).
expressions([]) --> [].




/*expression can be symble, number or expression between the left and right brackets
A number N is represented as n(N), a symbol S as s(S).
*/
expression(s(A))         --> symbol(Cs), { atom_chars(A, Cs) }.
expression(n(N))         --> number(Cs), { number_chars(N, Cs) }.
expression(Rest)         --> "(", expressions(Rest), ")". %dealing with brackets

%number is either a digit or a digit followed by numbers
number([D|Ds]) --> digit(D), number(Ds).
number([D])    --> digit(D).

digit(D) --> [D], { char_type(D, digit) }.
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
symbol is a symbol follow by symbolr 
(because symber have to begin with char_type: '2ed' for example is not valid symble)
symbol can sometimes begin with arithmetic operation

memberchk(?Elem, +List): True when Elem is an element of List.

char_type(?Char, ?Type):Tests or generates alternative Types or Chars
alnum
Char is a letter (upper- or lowercase) or digit.
alpha
Char is a letter (upper- or lowercase).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
symbol([A|As]) -->
    [A],
    { memberchk(A, "+/-*><=") ; char_type(A, alpha) },
    symbolr(As).

symbolr([A|As]) -->
    [A],
    { memberchk(A, "+/-*><=") ; char_type(A, alnum) },
    symbolr(As).
symbolr([]) --> [].

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Interpretation
   --------------
   The environment is represented as a pair of association
   lists Fs-Vs, associating function names with argument names and
   bodies, and variables with values. DCGs are used to implicitly
   thread the environment state through.
   
   empty_assoc(?Assoc)
	Is true if Assoc is the empty association list.
	
	maplist(:Goal, ?List)
	True if Goal can successfully be applied on all elements of List. 
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

run(Program, Values) :-
    parsing(Program, Forms0), %parse program input into expressions
    empty_assoc(E), % empty env
    compile_all(Forms0, Forms), %compile the expressions
    phrase(eval_all(Forms, Values0), [E-E], _), 
    maplist(unfunc, Values0, Values). %unfunc all the values

%unfunc return the original value of expression

unfunc(t, t).
unfunc(f, f). %boolean operation
unfunc(s(S), S).%simbol
unfunc(n(N), N). %number
unfunc([], []).
unfunc([Q0|Qs0], [Q|Qs]) :- unfunc(Q0, Q), unfunc(Qs0, Qs). %recursive unfunc case

/*arith(a,b,c,d) deals with the multiple inputs of arithmetic operations 
a is the expressions, b is the operation, c is the current value, d is the value of all expressions

example: (+ 3 4 5):
arith([3 4 5], +, 0, v) :- arith([4 5], +, 3, v) :- arith([5], +, 7, v) :- arith([], +, 12, v):- arith([], +, 12, 12)
*/
arith([], _, V, n(V)). %base: when there is no element left
arith([n(F)|Fs], Op, V0, V) :- E =.. [Op,V0,F], V1 is E, arith(Fs, Op, V1, V). %recursively remove the rest symbols

compile_all(Fs0, Fs) :- maplist(compile, Fs0, Fs). %compile_all is just apply compile on all of Fs0 and Fs

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    compile/2 marks (with "user/1") calls of user-defined functions.
    This eliminates an otherwise defaulty representation of function
    calls and thus allows for first argument indexing in eval//3.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

compile(F0, F) :-
    (   F0 = n(_)   -> F = F0 %numbers
    ;   F0 = s(_)   -> F = F0 %symbols
    ;   F0 = s(f)   -> F = f 
    ;   F0 = s(t)   -> F = t %boolean
    ;   F0 = s(null) -> F = [] %null
    ;   F0 = [] -> F = []
    ;   F0 = [s(define),s(Var),Val0] -> compile(Val0, Val), F = [define,Var,Val] %define expression
    ;   F0 = [s(Op)|Args0], 
        memberchk(Op, [+,-,*,equal,if,>,<,=,eval,list,car,cons,
                       cdr,not,isnull]) ->
        compile_all(Args0, Args),
        F = [Op|Args]
    ;   F0 = [s(definefunc),s(Name),Args0|Body0] -> %definefunc expression
        compile_all(Body0, Body),
        maplist(arg(1), Args0, Args), 
        F = [definefunc,Name,Args|Body]

    ;   F0 = [s(Op)|Args0] -> compile_all(Args0, Args), F = [user(Op)|Args]
    ).
%eval_all(a,b): evaluate both a and b
eval_all([], [])         --> []. %base case
eval_all([A|As], [B|Bs]) --> eval(A, B), eval_all(As, Bs).

eval(n(N), n(N))       --> []. %number evaluates to number
eval(t, t)             --> []. 
eval(f, f)             --> []. %bool evaluates to bool
eval([], [])           --> [].
eval(s(A), V), [Fs-Vs] --> [Fs-Vs], { get_assoc(A, Vs, V) }. %eval symbol by get_assoc in the env
eval([L|Ls], Value)    --> eval(L, Ls, Value). %recursively eval list

eval(+, As0, V)     --> eval_all(As0, As), { arith(As, +, 0, V) }.
eval(-, As0, V)     --> eval_all(As0, [n(V0)|Vs0]), { arith(Vs0, -, V0, V) }.
eval(*, As0, V)     --> eval_all(As0, Vs), { arith(Vs, *, 1, V) }.
eval(car, [A], C)   --> eval(A, V), { V == [] -> C = [] ; V = [C|_] }.
eval(cdr, [A], C)   --> eval(A, V), { V == [] -> C = [] ; V = [_|C] }. %car and cdr expression is the some as using [a|b] in prolog
eval(list, Ls0, Ls) --> eval_all(Ls0, Ls). %list
eval(isnull, [A], V)   --> eval(equal, [A,[]],V). %is null
eval(>, [A,B], V)   --> eval(A, n(V1)), eval(B, n(V2)), goal_truth(V1>V2, V).
eval(<, [A,B], V)   --> eval(>, [B,A], V).
eval(=, [A,B], V)   --> eval(A, n(V1)), eval(B, n(V2)), goal_truth(V1=:=V2, V).
eval(eval, [A], V)  --> eval(A, F0), { compile(F0, F1) }, eval(F1, V).
eval(equal, [A,B], V) --> eval(A, V1), eval(B, V2), goal_truth(V1=V2, V). %if A B are equal
eval(cons, [A,B], [V0|V1])  --> eval(A, V0), eval(B, V1). %cons just give [V0|V1]
eval(definefunc, [F,As|Body], s(F)), [Fs-Vs0] --> %user define function
    [Fs0-Vs0],
    { put_assoc(F, Fs0, As-Body, Fs)}. %put the user define function into the env

eval(user(F), As0, V), [Fs-Vs] --> 
    eval_all(As0, As1), %user define function call
    [Fs-Vs],
    { empty_assoc(E),
      get_assoc(F, Fs, As-Body),
      bind_arguments(As, As1, E, Bindings),
      phrase(eval_all(Body, Results), [Fs-Bindings], _),
	  last(Results, V)}.
	
%define a varible
eval(define, [Var,V0], V), [Fs0-Vs] -->
    eval(V0, V),
    [Fs0-Vs0],
    { put_assoc(Var, Vs0, V, Vs) }.
%base for if expression
eval(if, [Cond,Then|Else], Value) -->
    (   eval(Cond, f) -> eval_all(Else, Values), { last(Values, Value) }
    ;   eval(Then, Value)
    ).

	
goal_truth(Goal, T) --> { Goal -> T = t ; T = f }. % if goal is t T is t, otherwise T is f

%bind a list of arguments to a list of values
bind_arguments([], [], Bs, Bs). %base case, when there is not arguments to bind
bind_arguments([A|As], [V|Vs], Bs0, Bs) :-
    put_assoc(A, Bs0, V, Bs1),
    bind_arguments(As, Vs, Bs1, Bs).

	
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   test cases
   --------------
?- run(" (definefunc plus2(x) (define a 2) (+ a x) ) (plus2 4)", V).
V = [plus2, 6].

?- (run(" (definefunc fib (n) (if (= 0 n) 0 (if (= 1 n) 1 (+ (fib (- n 1)) (fib (- n 2)))))) (fib 24) ", V)).
V = [fib, 46368].

?- run(" (definefunc append (x y) (if (isnull x) y (cons (car x) (append (cdr x) y)))) (append (list 2 3) (list 3 4 5 6))", V).
V = [append, [2, 3, 3, 4, 5, 6]].

?- run("(cons 1 (list 2))",V).
V = [[1, 2]].

?- run("(cons (list 2) (list 2))",V).
V = [[[2], 2]].

?- run("(car (cdr (list 2 3 4)))",V).
V = [3].

?- run("(+ 2 3)",V).
V = [5].

?- run("(+ (* 3 2) 3)",V).
V = [9].

?- run("(= (* 3 2) 3)",V).
V = [f]
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

	
	 