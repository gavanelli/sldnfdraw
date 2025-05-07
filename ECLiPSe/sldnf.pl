% SLDNF Draw
% Produces a LaTeX drawing of an SLDNF tree
% Author: Marco Gavanelli
% https://docente.unife.it/marco.gavanelli

% Version 1.4
% Does not crash when printing infinite terms
% Uses lib(var_names) for pretty printing the names of variables.

% Version 1.5
% If the resolvent is too long (over max_resolvent_length/1 characters), prints it in two or more rows

% Version 1.6
% Animations
sldnf_version(1.6).

% TODO:
% stop when 1st solution found
% stop negation when 1st solution found
% CLP? Minimize?

:- lib(var_name).

% Note that it does not handle correctly the cut in the resolvent, but only
% in a clause. Please, do not write ?- p,!. but define e new predicate
% callp:- p,!.

% Given a clause a:-b,!,c, we have that:
% 1.the scope of the cut is a:-b, in the sense that it will cut the
%   alternatives to a and b. This is represented with the list
%   of OpenCuts: it contains all the cuts that are in a clause that
%   has been selected.
% 2.The cut has an effect when it is reached, and its effect lasts
%   until the backtracking goes back to a. Thus, the information about
%   reaching a cut is saved with assert(reached(Cut)).
%   Each cut has a unique name, given by a counter.

:- dynamic begin_resolvent/1.
:- dynamic end_resolvent/1.
:- dynamic begin_binding/1.
:- dynamic end_binding/1.
:- dynamic counter/1.
:- dynamic reached/2.
:- dynamic maxdepth/1.
:- dynamic current_slide/1.
:- dynamic fail_symbol/1.
:- dynamic cut_symbol/1.
:- dynamic success_symbol/1.
:- dynamic my_clause/2.
:- dynamic animations/1.

% Maximum length of the resolvent, in chars (very approximate)
% If the length exceeds this length, the resolvent will be printed on two (or more) lines
:- dynamic max_resolvent_length/1.
max_resolvent_length(25). 

set_depth(D):-
    retract(maxdepth(_)),
    assert(maxdepth(D)).

maxdepth(20). % Default max depth: 20

animations(no).

animate:- retract(animations(_)), assert(animations(yes)).

%begin_binding('{\\tt ').
%end_binding('}').

%begin_resolvent('{\\color{blue} ').
%end_resolvent('}').

%cut('{\\color{red} (cut)}').
%cut('{\\color{red} $\\nrightarrow$}').
cut_symbol('(cut)').

%fail_symbol("$\\bot$").
%fail_symbol("{\\color{red} false}").
fail_symbol("false").

success_symbol("true").

d(G):- draw_goal(G,"tree.tex").

ds(G):- animations(yes),!,d(G), system('./animateTree.sh').
ds(G):- d(G), system('./drawTree.sh').

draw_goal(G,FileName):-
    init_file(FileName,write,File),
    term_length_chopped(G,Length),
    conv_sq_list(G,GSq),
    init_cuts,
	reset_slide,
    (draw(GSq,File,Length) ; true),
    close(File).

draw(R,F,Longest):-
    maxdepth(Depth),
    draw(R,F,Longest,Depth,[]).

% draw(+Resolvent,+Stream,MaxLenghtOfResolvent,MaxDepth,OpenCuts)
draw([],F,Longest,_,_):-
	success_symbol(SuccessSymbol),
    print_string_spaces(F,Longest,SuccessSymbol),
    fail.
draw(_,F,Longest,Depth,_):- Depth=<0, !,
    print_string_spaces(F,Longest,"..."),
    fail.
draw([not G|R],F,LongestIn,Depth,OpenCuts):-
    Depth1 is Depth-1,
    write_indented(F,Depth,"\\begin{bundle}{"),
    print_resolvent(F,[not G|R]),
    writeln(F,"}"),
	write_indented(F,Depth,"\\chunk{"),
    % NOTA: forse in questo caso non conviene metterlo, cosi` il box diventa giusto.
    %       pero` non si assicura che sia giusto il figlio del box...
    % Compute the maximum length
    term_length_chopped([not G|R],ResLen), Length is max(LongestIn,ResLen),
	write_indented(F,Depth,"\\begin{bundle}{\\framebox{"),
    (draw([G],F,0,Depth1,[]) ; true),
    write(F,"}}"),
	max_subtree_width([G],MaxWidthTemp),
	MaxWidth is fix(1.3*max(MaxWidthTemp,Length)),
    (vanilla(G)
      ->    print_fail(F,Depth,MaxWidth) %MODIFIED: ResLen
      ;     write_indented(F,Depth,"\\chunk{"), start_pause(F),
                (draw(R,F,MaxWidth,Depth1,OpenCuts); true), end_pause(F), write(F,"}")
    ),
    indent(F,Depth),writeln(F,"\\end{bundle}"),
	%end_pause(F),
	indent(F,Depth),writeln(F,"}\\end{bundle}"),
	%end_pause(F),
    fail.

% Cut !
draw([!|R],F,LongestIn,Depth,[LastCut|OpenCuts]):- !,
    Depth1 is Depth-1,
    term_length_chopped([!|R],ResLen), Length is max(LongestIn,ResLen),
    write_indented(F,Depth,"\\begin{bundle}{"),
    print_resolvent(F,[!|R]),
    writeln(F,"}"),
	current_slide(Slide),
    assert(reached(LastCut,Slide)),
    (print_builtin_children(true,R,F,Length,Depth1,OpenCuts);     writeln(F,"\\end{bundle}")), 
    fail.    

% Conjunction of goals: may occur inside another predicate, like not((G1,G2)).
draw([(G1,G2)|R],F,LongestIn,Depth,OpenCuts):-
    draw([G1,G2|R],F,LongestIn,Depth,OpenCuts).

% Built-in Predicate
draw([G|R],F,LongestIn,Depth,OpenCuts):-
    Depth1 is Depth-1,
    not(G = not(_)),
    not(G=(_,_)),
    built_in(G),
    term_length_chopped([G|R],ResLen), Length is max(LongestIn,ResLen),
    write_indented(F,Depth,"\\begin{bundle}{"),
    print_resolvent(F,[G|R]),
    writeln(F,"}"),
    (print_builtin_children(G,R,F,Length,Depth1,OpenCuts);     write_indented(F,Depth,"\\end{bundle}")), 
    fail.    

% User defined predicate
draw([G|R],F,LongestIn,Depth,OpenCuts):-
    Depth1 is Depth-1,
    not(G = not(_)),
    not(G=(_,_)),
    not(built_in(G)),
%	max_subtree_width([G|R],MaxWidthTemp),
    term_length_chopped([G|R],ResLen), Length is max(LongestIn,ResLen),
	write_indented(F,Depth,"\\begin{bundle}{"),
    print_resolvent(F,[G|R]),
    writeln(F,"}"),
    (print_children(G,R,F,Length,Depth1,OpenCuts);     indent(F,Depth), writeln(F,"\\end{bundle}") %,end_pause(F) 
	), 
    fail.

print_children(G,R,F,Length,Depth,OpenCuts):-
    %Depth1 is Depth-1,
    term_variables(G,Vars),
    vars_names(Vars,VarNames),
    count_children(G,NumChildren),
    (NumChildren = 1 -> Len = Length ; Len=0),
    increase_counter, get_counter(C), 
    % Unique name for the node: if a cut is reached, it will have this name
    % First part: the cut may cut the alternatives for the clause
    retract_cut_on_backtracking(C),
    clausola(G,B),

%%% QUI SI POTREBBE:
% 1. mettere un secondo parametro nel predicato dynamic reached: e` il numero della slide in cui il cut viene incontrato (viene incontrato nella draw([!|...)
% 2. cambiare questa clause_is_not_cut in una clause_is_cut (controllare che non ci siano variabili che vengono legate in questo ...)
% 3. la clause_is_cut restituisce anche la slide S in cui viene fatto il taglio
% 4. cambiare la start_pause in una pausa effettuata alla slide S
% 5. sincronizzare anche le slide seguenti (se necessario)
    (clause_is_cut(C,SlideCut)	%ATTENZIONE CHE HO TOLTO UNA NEGAZIONE! CONTROLLARE CHE NON CI SIANO DEI BINDING ...
        ->   write_indented(F,Depth,"\\chunk{"),start_pause(F,SlideCut), cut_symbol(StringCut), write(F,StringCut),write(F,"}"), end_pause(F), fail
		;    true),
    (check_body_contains_cut(B,OpenCuts,NewCuts,_AddedCut,C)
        ->    % retract_cut_on_backtracking(AddedCut)
              true
        ;     NewCuts=OpenCuts),
    % Second part: takes care of the alternatives of the predicates
    % in the body
    ( (member(Cut,OpenCuts),reached(Cut,SlideCut))
      ->        write_indented(F,Depth,"\\chunk{"),start_pause(F,SlideCut), cut_symbol(StringCut), write(F,StringCut),write(F,"}"),  end_pause(F), fail
      ;         write_indented(F,Depth,"\\chunk"),
                print_binding(F,VarNames),
                write(F,"{"), start_pause(F),
                append(B,R,Ris),
                (draw(Ris,F,Len,Depth,NewCuts) ; indent(F,Depth), end_pause(F), write(F,"}"), fail)
    ).

print_children(G,_,F,Length,Depth,_):-
    not(clausola(G,_)),
    print_fail(F,Depth,Length),
    fail.

print_builtin_children(G,R,F,Length,Depth,OpenCuts):-
%    Depth1 is Depth-1,
    term_variables(G,Vars),
    vars_names(Vars,VarNames),
    findall(G,call(G),L),length(L,NumChildren),
    (NumChildren = 1 -> Len = Length ; Len=0),
    call(G),
    write_indented(F,Depth,"\\chunk"),
    print_binding(F,VarNames),
    write(F,"{"),start_pause(F),
    (draw(R,F,Len,Depth,OpenCuts) ; end_pause(F), write(F,"}"), fail).
print_builtin_children(G,_,F,Length,Depth,_OpenCuts):-
    not(call(G)),
    print_fail(F,Depth,Length),
    fail.

%%%%%%%%%%%%%%%% Predicates fot cut handling %%%%%%%%%%%%%%%%%

%check_body_contains_cut(+Body,++OpenCuts,-NewCuts,-AddedCut,++Counter)
check_body_contains_cut(B,OpenCuts,NewCuts,AddedCut,Counter):-
    memberchk(!,B),push_cut(OpenCuts,NewCuts,AddedCut,Counter).


% A clause is not cut if the cut of the current
% node has not been reached.
clause_is_not_cut(C):-
    not reached(cut(C)).
clause_is_cut(C,Slide):-
    reached(cut(C),Slide).

push_cut(L,[cut(C)|L],cut(C),C).

% On backtracking, remove the information about the reached cuts
% that are not open
retract_cut_on_backtracking(_).
retract_cut_on_backtracking(C):-
    retract(reached(C,_)), fail.

follows(cut(N),cut(N1)):-
    N>N1.

last_cut([C],C):-!.
last_cut([Cut|Cuts],C):-
    last_cut(Cuts,LastSoFar),
    (follows(LastSoFar,Cut)
        ->  C=LastSoFar
        ;   C=Cut).

init_cuts:- retract_all(reached(_,_)),
    reset_counter.

increase_counter:-
    counter(C), retract(counter(C)), C1 is C+1,
    assert(counter(C1)).
get_counter(C):- counter(C).
reset_counter:- retract_all(counter(_)),
    assert(counter(0)).

%%%%%%%%%%%%%%% End predicates for cut handling %%%%%%%%%%%%%%

%%%%%%%%%%%%%%%% Predicates for animations %%%%%%%%%%%%%%%%%%
start_pause(_):- animations(no),!.
start_pause(F):-
	current_slide(S),
	start_pause(F,S).
start_pause(_,_):- animations(no),!.
start_pause(F,S):-
	write(F,"\\uncover<"),write(F,S),write(F,"->{"),increase_slide.

end_pause(_):- animations(no),!.
end_pause(F):-
	write(F,"}").
	
increase_slide:-
    current_slide(C), retract(current_slide(C)), C1 is C+1,
    assert(current_slide(C1)).
reset_slide:- retract_all(current_slide(_)),
    assert(current_slide(2)).
%%%%%%%%%%%%%%%% End Predicates for animations %%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%% Utilities %%%%%%%%%%%%%%

write_indented(F,N,S):- indent(F,N), write(F,S).

% Helpful for indentation, so that the LaTeX code is slightly more readable
indent(F,N):- nl(F), maxdepth(Max), N1 is Max-N, indentloop(F,N1).
indentloop(_,0):- !.
indentloop(F,N):- write(F,' '), N1 is N-1, indentloop(F,N1).


count_children(G,NumChildren):-
    findall(B,clausola(G,B),L),
    length(L,NumChildren).

vars_names([],[]).
vars_names([X|T],[b(X,N)|TN]):-
    var_name(X,N),
    vars_names(T,TN).

term_to_string(Term,String):-
    open(string(""),write,Stream),
    write(Stream,Term),
    get_stream_info(Stream, name, String),
    close(Stream).

var_name(X,N):-
    get_var_name(X,N),!.
var_name(X,NewName):-
    term_to_string(X,N),
    (var(X)
     -> % if the variable name starts with underscore, set X as its name
        (string_list(N,[95|_]) -> set_var_name(X,'X') 
            ; set_var_name(X,N)),
        get_var_name(X,NewName)
     ;  NewName=N).

print_binding(F,X):-
    write(F,"["),
    (begin_binding(S) -> write(F,S); true),
    print_binding1(F,X),
    (end_binding(Send) -> write(F,Send) ; true),
    write(F,"]").

print_binding1(_F,[]).
print_binding1(F,[b(A,B)|T]):-
    var_name(A,Name),
    Name = B, !,
    % Avoid writing "X=X" as a binding...
    print_binding1(F,T).
print_binding1(F,[b(A,B)|T]):-
    write_var(F,B), write(F,"/"),
    (acyclic_term(A)
      ->    write_term_no_sqbrack(F,A,1000)
      ;     maxdepth(D), write_term_no_sqbrack(F,A,D)
    ), 
    (T=[] -> true
        ; write(F,", "), print_binding1(F,T)).

write_var(F,V):-
    var(V),
    var_name(V,VarName),!,
    split_string(VarName,"#","",[Name,Number]),
    write(F,"$"),
    write(F,Name),
    write(F,"_{"),
    write(F,Number),
    write(F,"}$").
write_var(F,VarName):-
    string(VarName),
    split_string(VarName,"#","",[Name,Number]),!,
    write(F,"$"),
    write(F,Name),
    write(F,"_{"),
    write(F,Number),
    write(F,"}$").

% Writes a term replacing the symbols "[" and "]"
% with \lbrack and \rbrack, because you cannot use "["
% inside a label of an arc.
% Stops at depth Depth
% write_term_no_sqbrack(File,Term,Depth):-
write_term_no_sqbrack(F,_,0):- !,
    write(F,"\\dots").
write_term_no_sqbrack(F,A,_):-
    % Named Variables
    var(A), !,
    write_var(F,A).
write_term_no_sqbrack(F,[],_):- !,
    write(F,"\\lbrack\\rbrack ").
write_term_no_sqbrack(F,[H|T],N):- !,
    write(F,"\\lbrack "),
    print_list_no_sqbrack(F,[H|T],N),
    write(F,"\\rbrack ").
write_term_no_sqbrack(F,T,_):- 
    T =.. [Fun], !,
    write(F,Fun).
% infixed operators
write_term_no_sqbrack(F,T,N):-
    T =.. [Fun,ArgX,ArgY],
    N1 is N-1,
    current_op(_,Associativity,Fun),
    (Associativity = xfy ; Associativity = yfx ; Associativity = xfx),!,
    write_term_no_sqbrack(F,ArgX,N1),
    pretty_write_op(F,Fun),
    write_term_no_sqbrack(F,ArgY,N1).
write_term_no_sqbrack(F,T,N):- !,
    N1 is N-1,
    T =.. [Fun|Arg],
    write(F,Fun),
    write(F,"("),
    print_list_no_sqbrack(F,Arg,N1),
    write(F,")").

% If the list is a difference list, we also have the 
% case in which the rest is a variable.
%print_list_no_sqbrack(File,Term,Depth)
print_list_no_sqbrack(F,V,N):-
    var(V), !,
    write_term_no_sqbrack(F,V,N).
print_list_no_sqbrack(F,[H|T],N):-
    var(T),!,
    write_term_no_sqbrack(F,H,N),
    write(F,"$|$"),
    write_term_no_sqbrack(F,T,N).
print_list_no_sqbrack(F,[H],N):- !,
    write_term_no_sqbrack(F,H,N).
print_list_no_sqbrack(F,[H1,H2|T],N):-
    N1 is N-1,
    write_term_no_sqbrack(F,H1,N1),write(F,","),
    print_list_no_sqbrack(F,[H2|T],N1).

pretty_write_op(F,<):- !,
    write(F,$<$).
pretty_write_op(F,=<):- !,
    write(F,$=<$).
pretty_write_op(F,>=):- !,
    write(F,$>=$).
pretty_write_op(F,>):- !,
    write(F,$>$).
pretty_write_op(F,is):- !,
    write(F," is ").
pretty_write_op(F,\=):- !,
    write(F,"$\\backslash=$").
pretty_write_op(F,Op):- !,
    write(F,Op).

print_resolvent(F,X):-
    max_resolvent_length(MaxLength),
	print_resolvent(F,X,MaxLength).
print_resolvent(F,X,MaxLength):-
    (begin_resolvent(S) -> write(F,S); true),
    term_length(X,Len),
    (X=[_,_|_], Len>MaxLength
    ->  write(F,"\\begin{tabular}{c}"),
        print_list_tabular(F,X),
        write(F,"\\end{tabular}")
    ;    print_list(F,X)
    ),
    (end_resolvent(Send) -> write(F,Send) ; true).

% Prints a list in a tabular environment, without exceeding max_resolvent_length in each row
print_list_tabular(F,[A]):-!, print_list(F,[A]).
print_list_tabular(F,X):-
    append2(First,Rest,X),
    (First = [_]
     -> true
     ;  term_length(First,Len1),
        max_resolvent_length(MaxLength),
        Len1<MaxLength
    ),!,
	print_list(F,First),
    (Rest=[] -> true
     ;  write(F,",\\\\"),
        print_list_tabular(F,Rest)
    ).

% Like append, but provides the solutions in the opposite order
% i.e., if the third argument is ground and the others are not,
% first provides the longest lists as first aruments
append2([H|T],X,[H|S]):-
    append2(T,X,S).
append2([],X,X).


print_list(F,[H]):- !,
    maxdepth(D),
    write_term_no_sqbrack(F,H,D).
print_list(F,[H1,H2|T]):-
    maxdepth(D),
    write_term_no_sqbrack(F,H1,D),write(F,","),
    print_list(F,[H2|T]).

print_fail(F,Depth,Longest):-
    write_indented(F,Depth,"\\chunk{"),
	start_pause(F),
	fail_symbol(FailSymb),
	print_string_spaces(F,Longest,FailSymb),
	end_pause(F),
    write(F,"}").

% Prints a string adding "Longest" spaces.
print_string_spaces(F,Longest,String):-
	string_length(String,StringLength),
    NumSpace is (Longest-StringLength)//2,
	%write(F,NumSpace),
    print_n_spaces(F,NumSpace),
    write(F,String), %writeln(F,"\n"), 
    print_n_spaces(F,NumSpace).
	%write(F,NumSpace).

print_n_spaces(_,N):- N=<0,!.
print_n_spaces(F,N):-
    number(N), N>0,
    write(F,"~"),
    N1 is N-1,
    print_n_spaces(F,N1).

vanilla([]).
vanilla([A|B]) :- !, vanilla(A), vanilla(B).
vanilla(not X) :- !,
    (vanilla(X) -> fail ; true).
vanilla(X) :-
    built_in(X), call(X).
vanilla(X) :-
    clausola(X,Body),
    vanilla(Body).

term_length(G,Length):-
    term_to_string(G,S), 
    string_length(S,Length).

term_length_chopped(G,L):-
    max_resolvent_length(MaxTermLength),
    term_length(G,Length),
    (Length=<MaxTermLength
    ->  L=Length
    ;   L=MaxTermLength
    ).

% max_subtree_width(G,Width):-
max_subtree_width([],0):-!.
max_subtree_width([not A|B],Width):-!,
	term_length_chopped([not A|B],W1),
	findall(W,
		(	max_subtree_width([A],W)
		),
		LW),
	Width is max(sum(LW),W1).
max_subtree_width([A|B],Width):- built_in(A),!,
	term_length_chopped([A|B],W1),
	findall(W,
		(	call(A),
			max_subtree_width(B,W)
		),
		LW),
	Width is max(sum(LW),W1).

	
max_subtree_width([A|B],Width):-!,
	term_length_chopped([A|B],W1),
	findall(W,
		(	clausola(A,Body),
			append(Body,B,Resolvent),
			max_subtree_width(Resolvent,W)
		),
		LW),
	Width is max(sum(LW),W1).
	    
/*
max_subtree_width([A|B],W):-!,
	max_subtree_width(A,WA),
	max_subtree_width(B,WB),
	W is max(WA,WB).	% Very approximate; in principle the resolvent is WA+Length(B) while resolving A, then it will be chopped ...
max_subtree_width(not A,W):- !,max_subtree_width(A,W).
max_subtree_width(A,Width):- !,
	built_in(A),
	findall(W,
		(call(A),
		 term_length_chopped(A,W)
		),LW),
	Width is sum(LW).
max_subtree_width(X,Width) :-
	findall(W,
		(	clausola(X,Body),
			max_subtree_width(Body,W)
		),
		LW),
	Width is sum(LW).
*/



remove_char(Sin,Char,Sout):-
    split_string(Sin,Char,"",SubStrings),
    concat_string(SubStrings,Sout).

clausola(H,BSq):-
    functor(H,F,A), current_predicate(F/A),
    clause(H,B),
    conv_sq_list(B,BSq).
clausola(H,BSq):-
    my_clause(H,BSq).

conv_sq_list((A,B),[A|Bsq]):- !,
    conv_sq_list(B,Bsq).
conv_sq_list(true,[]):- !.
conv_sq_list(X,[X]).

built_in(G):-
    functor(G,F,A),
    current_built_in(F/A).

init_file(FileName,write,File):-
    open(FileName,write,File),
    write(File,"% File created by SLDNF Draw version "),
    sldnf_version(Ver),
    writeln(File,Ver),
    writeln(File,"% http://endif.unife.it/it/ricerca-1/aree-di-ricerca/informazione/ingegneria-informatica/software/sldnf-draw"),
    nl(File).
