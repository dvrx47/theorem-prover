/* Funktory do budowania klauzul */

:- op(200, fx, ~).
:- op(500, xfy, v).

/* Główny program: main/1. Argumentem jest atom będący nazwą pliku
 * z zadaniem. Przykład uruchomienia:
 *    ?- main('zad125.txt').
 * Plik z zadaniem powinien być plikiem tekstowym, na którego
 * początku znajduje się lista klauzul zbudowanych za pomocą funktorów
 * v/2 i ~/1 (szczegóły znajdują się w opisie zadania). Listę zapisujemy
 * w notacji prologowej, tj. rozdzielając elementy przecinkami
 * i otaczając listę nawiasami [ i ]. Za nawiasem ] należy postawić
 * kropkę. Wszelkie inne znaki umieszczone w pliku są pomijane przez
 * program (można tam umieścić np. komentarz do zadania).
 */

main(FileName) :-
   readClauses(FileName, Clauses),
   prove(Clauses, Proof),
   writeProof(Proof).

%---------------------------
append([], X, X).
append([H|T], X, [H|Y]) :-
append(T, X, Y).

oznaczKlauzule(Clauses, Out) :- oznaczKlauzule( Clauses, [], Out, 0 ), !.
oznaczKlauzule([], X, X, _).
oznaczKlauzule( [A|B], X, Out, N ) :- 
	Next is N+1, 
	append(X, [(A, Next, z(axiom))], R), 
	oznaczKlauzule( B, R, Out, Next).

zlozona( _ v _ ).
literal( X ) :- not( zlozona( X ) ).

getLiteral(X, Res) :- literal(X), Res = X.
getLiteral(A v _, Res) :- getLiteral( A, Res).
getLiteral(_ v B, Res) :- getLiteral( B, Res).

delLiteral( Literal, Literal v B, B) :- !.
delLiteral( Literal, A v Literal v B, A v B) :- !.
delLiteral( Literal, A v Literal, A).

przepisz( A, L ) :- przepisz( A, [], X ), sort(X, L), !.
przepisz( A, L, Res ) :- literal(A), !, append(L, [A], Res).
przepisz( A, L, Res ) :- 
	getLiteral(A, X), 
	delLiteral(X, A, B), 
	append(L, [X], L0), 
	przepisz( B, L0, Res ).

nmember(_, []) :- !.
nmember(A, [H|T]) :- A \= H, nmember( A, T ).

bezSprzecznosci([]).
bezSprzecznosci([H|T]) :- H = ~X, !, not( member(X, T) ), bezSprzecznosci(T).
bezSprzecznosci([H|T]) :- not( member(~H, T) ), bezSprzecznosci(T). 

bezPowtorzen(A, B, Res) :- bezPowtorzen( A, B, [], Res), !.
bezPowtorzen([], [], Res, Res):- !.
bezPowtorzen( [], A, L, Res ) :- !, bezPowtorzen( A, [], L, Res ). 
bezPowtorzen([H|T], A, L, Res) :- nmember(H, T), nmember(H, A), !, append( L, [H], X), bezPowtorzen( T, A, X, Res).
bezPowtorzen([_|T], A, L, Res) :- bezPowtorzen( T, A, L, Res ).

naKlauzule([H|T], Res) :- naKlauzule( T, H, Res ), !.
naKlauzule( [], Res, Res ) :- !.
naKlauzule([A|T], X, Res ) :- naKlauzule( T, A v X, Res ).

zlacz( E, F, Res ) :- 
	przepisz( E, L ), 
	przepisz(F, L2), 
	bezPowtorzen(L, L2, L3),
	naKlauzule(L3, Res).

porownaj(X, Y, Res ) :-
	literal(X), zlozona(Y),
	getLiteral(Y, A),
	A = ~X,
	delLiteral(~X, Y, Res), !.

porownaj(~X, Y, Res ) :-
	literal(X), zlozona(Y),
	getLiteral(Y, X),
	delLiteral(X, Y, Res).

porownaj(X, Y, Res) :- 
	literal(Y), zlozona(X), !,
	porownaj(Y, X, Res).

porownaj(X, Y, Res) :-
	getLiteral(X, A),
	getLiteral(Y, B),
	B = ~A,
	delLiteral(A, X, E),
	delLiteral(B, Y, F),
	zlacz( E , F, Res ).

porownaj(X, Y, Res) :-
	getLiteral(X, B),
	getLiteral(Y, A),
	B = ~A,
	delLiteral(B, X, E),
	delLiteral(A, Y, F),
	zlacz( E , F, Res ).	

wyznaczNumer(L, Numer) :- wyznaczNumer(L, 1, Numer), !.
wyznaczNumer([], Numer, Numer).
wyznaczNumer([_|B], X, Numer) :- Next is X+1, wyznaczNumer(B, Next, Numer).

nmember2(_,[]) :- !.
nmember2(A,[B|D]) :- B = (X,_,_), A\=X, nmember2(A,D).

dopiszMozliwosci( _, [], Res, Res ) :- !.
dopiszMozliwosci( A, [H|T], L, Res ) :- 
	(N, N1, _) = A,
	(M, M1, _) = H,
	porownaj( N, M, Odp ), 
	nmember2( Odp, L ), !,
	Odp \= ~(~_),
	wyznaczNumer(L, Numer),
	append(L, [(Odp, Numer, z(N1, M1))], X), 
	dopiszMozliwosci( A, [H|T], X, Res ).
dopiszMozliwosci( A, [_|T], L, Res ) :- dopiszMozliwosci( A, T, L, Res ). 

canProve(L) :- L \= [], canProve(L, L), !.
canProve( [X|_], L ) :- X = (A,_,_), literal(A), member( (~A,_,_), L ).
canProve( [X|_], L ) :- X = (~A,_,_), literal(A), member( (A,_,_), L).
canProve([X|Y], [X|Y]) :- canProve(Y, Y).


udowodnij( Proof, End ) :- udowodnij( Proof, Proof, End), !.
udowodnij( Proof, [X|B], End ) :- 
	X = (A,A1,_),
	literal(A),
	member((~A, A2,_), B),	
	wyznaczNumer( Proof, N ),
	append(Proof, [([], N, z(A1, A2))], End).

udowodnij( Proof, [X|B], End ) :- 
	X = (~A,A1,_),
	literal(A),
	member((A, A2,_), B),	
	wyznaczNumer( Proof, N ),
	append(Proof, [([], N, z(A1, A2))], End).
udowodnij(Proof, [_|Y], End) :- udowodnij(Proof, Y, End).

udowodnij(Proof, L, [_|B], End) :- udowodnij(Proof, L, B, End).
udowodnij( Proof, [_|T], L, End ) :- udowodnij( Proof, T, L, End ).

poprawFormat(Res, Proof) :- poprawFormat(Res, [], Proof), !.
poprawFormat([], Proof, Proof).
poprawFormat([A|B], L, Proof) :- A = (X,_,z(Y)), !, append(L, [(X,Y)], Out), poprawFormat(B, Out, Proof).
poprawFormat([A|B], L, Proof) :- A = (X,_,z(Y,Z)), !, append(L, [(X,Y,Z)], Out), poprawFormat(B, Out, Proof). 

prove( Clauses, Proof ) :- oznaczKlauzule(Clauses, Out), prove(Out, Out , Res), poprawFormat(Res, Proof).
prove( _, Proof, End) :- canProve(Proof), udowodnij(Proof, End). 
prove( [A | B], L, Proof ) :- dopiszMozliwosci( A, B, L, Res ), fix(B, Res, S), prove( S, Res, Proof ).

fix( [A|_], [A|C], S ) :- S = [A|C], !.
fix( [A|B], [_|D], S ) :- fix([A|B], D, S). 
%-----------------------

readClauses(FileName, Clauses) :-
   open(FileName, read, Fd),
   read(Fd, Clauses),
   close(Fd).

/* Wypisywanie dowodu */

writeProof(Proof) :-
   maplist(clause_width, Proof, Sizes),
   max_list(Sizes, ClauseWidth),
   length(Proof, MaxNum),
   write_length(MaxNum, NumWidth, []),
   nl,
   writeClauses(Proof, 1, NumWidth, ClauseWidth),
   nl.

clause_width((Clause, _), Size) :-
   write_length(Clause, Size, []).

writeClauses([], _, _, _).
writeClauses([(Clause,Origin) | Clauses], Num, NumWidth, ClauseWidth) :-
   format('~t~d~*|.  ~|~w~t~*+  (~w)~n',
          [Num, NumWidth, Clause, ClauseWidth, Origin]),
   Num1 is Num + 1,
   writeClauses(Clauses, Num1, NumWidth, ClauseWidth).
