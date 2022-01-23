(*
Programme de r�solution du jeu "Le Compte est bon",
issu de l'�mission "Des Chiffres et des Lettres".


#On fournit au joueur (ici au programme):
-un r�sultat : r, un entier avec r appartenant � [100,999]
-une liste d'entiers : l, telle que :
Elle contient 6 nombres, dont : 
des �l�ments de [1,10], qui peuvent chacun intervenir 2 fois maximum,
des �l�ments de {25;50;75;100}, qui peuvent chacun intervenir 1 fois maximum,
exemple : [1;5;100;7;1;25]


#R�gles du jeu :
A partir des �l�ments de l, le joueur doit arriver au le r�sultat, en respectant : 
1) il ne doit utiliser qu'une seule fois chaque �l�ment de l.
2) il peut combiner les �l�ments de l entre eux en utilisant les op�rations arithm�tiques 
(+, -, *, /), mais en ayant comme r�sultats interm�diaires, que des entiers naturels (positifs!).


#Mon programme r�sout ce jeu, mais il r�sout aussi avec des r�gles plus larges :
-On peut lui fournir une listes l d'entiers, de taille quelconque, et d'entiers quelconques.
-On peut lui fournir un r�sultat quelconque (seule condition : diff�rent de 0).


#Attention tout de m�me, si on augmente la taille de l, les temps de calcul sont d�cupl�s,
je vous conseille alors d'utiliser le programme "resol_rapide" qui pourra r�soudre dans un temps
encore acceptable si l n'est pas trop grande, mais il ne renvoit pas la solution optimale.

#Pour une utilisation respectant les r�gles du jeu, le programme "solution_chiffre_dcdl"
renvoit la solution optimale.
*)





type partie = P of int list * int * string list;;
type sol = Pas_de_sol | S of int * string * bool;;



(*Tout d'abord on cr�e une fonction de tri (reprenant le tri fusion) qui tri une liste d'entier
et, en parall�le fait les m�me op�ration � une seconde liste, de m�me taille,
� fin que la bijection qui existait avant le tri entre les deux liste 
(qui � l'�l�ment i de la liste 1 associe l'�l�ment i de la liste 2) soit conserv�e.

l est la liste 1, s est la liste 2*)

let rec fusion c1 c2 = match (c1, c2) with
   | (([], s1), (l2, s2)) -> (l2, s2)
   | ((l1, []), (l2, s2)) -> (l2, s2)
   | ((l1, s1), ([], s2)) -> (l1, s1)
   | ((l1, s1), (l2, [])) -> (l1, s1)
   | ((p1 :: q1, sp1 :: sq1), (p2 :: q2, sp2 :: sq2)) ->
      if p1 > p2 then
         match fusion c1 (q2, sq2) with
         | (l, s) -> (p2 :: l, sp2 :: s)
      else
         match fusion (q1, sq1) c2 with
         | (l, s) -> (p1 :: l, sp1 :: s);;


let separe l s =
   let n = (List.length l) / 2 in
      let rec aux l1 s1 n1 = match (l1, s1, n1) with
         | (_, _, 0) -> (([], []), (l1, s1))
         | ([], _, _) -> (([], []), ([], []))
         | (_, [], _) -> (([], []), ([], []))
         | (p :: q, sp :: sq, n1) -> match aux q sq (n1 - 1) with
            | ((l2, s2), (l3, s3)) ->
               ((p :: l2, sp :: s2), (l3, s3)) in
         aux l s n;;


let rec tri_fusion l s = match l with
   | [] -> ([], [])
   | [a] -> ([a], s)
   | _ -> match separe l s with
      | ((l1, s1), (l2, s2)) -> fusion (tri_fusion l1 s1) (tri_fusion l2 s2);;

(*En fait, la bijetion liant l et s est f : l'�l�ment i de l est reprensent� par une chaine de caract�re,
plac�e � la position i dans s, s une string list. Exemple : 4 peut �tre represent� dans s par "(25/5)-1"
Comme vu ci-dessus, dans toute la suite du programme 
on va maintenir l'invariant : f est une bijection de l dans s*)



(*la fonction "max_possible" associe � une partie p (un r�sultat r et une liste l),
une solution qui est l'entier maximal que l'on peut obtenir � partir de la liste l
en respectant les r�gles du jeu.
Cette fonction permet de d�terminer rapidement si pour une partie donn� on peut trouver le compte
bon ou non,
et si non, elle fournit la meilleur approche.*)

let rec max_possible p = match p with
   | P (l, r, s) -> match (l,s) with
      | ([],_) -> Pas_de_sol
      |(_,[]) -> Pas_de_sol
      | (1 :: 1 :: p1 :: p2 :: q, s1::s2::s3::s4::s5) ->
         begin
            match max_possible (P (q,r,s5)) with
            | Pas_de_sol -> 
      			let n = (p1 + 1) * (p2 + 1) in
      			S (n, "(" ^ s3 ^ "+"^ s1 ^")*(" ^ s4 ^ "+"^ s2 ^")", n=r)
            | S (a, b, s0) -> 
            let n = (p1 + 1) * (p2 + 1) * a in
            S (n, "(" ^ s3 ^ "+"^s1^")*(" ^ s4 ^ "+"^ s2 ^")*" ^ b, n=r)
         end
      | (1 :: p :: q, s1::s2::s3) ->
         begin
            match max_possible (P (q,r,s3)) with
            | Pas_de_sol ->
            let n = (p + 1) in
            S (n, "(" ^ s2 ^ "+"^s1^")", n=r)
            | S (a, b, s0) ->
            let n = (p + 1) * a in
            S (n, "(" ^ s2 ^ "+"^s1^")*" ^ b, n=r)
         end
      | (p :: q, s1::s2) ->
         begin
            match max_possible (P (q,r,s2)) with
            | Pas_de_sol -> S (p, s1, r=p)
            | S (a, b, s0) -> 
            let n = p * a in
            S (n, s1 ^ "*" ^ b, n=r)
         end;;
max_possible (P ([1;1;2;3;4;5;6], 18, ["1";"1";"2";"3";"4";"5";"6"]));;


let permute_circulaire l = match l with
|[]-> l
|p::q-> q@[p];;



(*la fonction de resolution du jeu va toujours effectuer une op�ration au deux premiers �l�ments 
de la liste l, on cr�er donc un tableau des permutations de la liste l, telle que tout les couples
faisables � partir d'�l�ments de l soit une fois et une seule en t�te d'une des permutation.
"tab_de_permut" associe � l son tableau de permutation*)

let tab_de_permut l=
   let n0 = List.length l in
      let n = (n0 * (n0 - 1) / 2) in
         let tab = Array.make n [] in
            let rec remplit l1 k t =
               let m = List.length l1 in
                  match l1 with
                  | [] -> ()
                  | [a] -> ()
                  | p :: q ->
                     begin
                        let q1 = ref q in
                           for i = 0 to (m - 2) do
                              tab.(i + k) <- (p :: !q1 @ t);
                              q1 := permute_circulaire !q1 done;
                           remplit q (k + m - 1) (p :: t)
                     end in
               remplit l 0 [];
               (tab, n);;



(*Comme dit pr�c�demment, on va effectuer une op�ration aux deux premiers �l�ments de l : a1 et a2,
leur repr�sentaion dans s sont ts1 et ts2. Le programme "ope" va associer � a1 et a2 l' entier a1+a2, ou a1-a2,
ou a2-1,etc; j, un entier entre 0 et 5, d�termine selon sa valeur quelle op�ration est effectu�e*)

let ope a1 a2 j ts1 ts2=
(*effectue les diff�rentes op�rations possibles entre a1 et a2, tout en respectant les r�gles du jeu*)
   if j = 0 then S(a1 + a2, "(" ^ ts1 ^ "+" ^ ts2 ^ ")", true)
   else if j = 1 then
      begin
         let c = a1 - a2 in
            if c > 0 then S(c, "(" ^ ts1 ^ "-" ^ ts2 ^ ")", true)
            else Pas_de_sol
      end
   else if j = 2 && a1<>1 && a2<>1 then S(a1 * a2, "(" ^ ts1 ^ "*" ^ts2 ^ ")", true)
   else if j = 3 then
      begin
         if a1 mod a2 = 0 && a2<>1 then S(a1 / a2, "(" ^ ts1 ^ "/" ^ ts2 ^ ")", true)
         else Pas_de_sol
      end
   else if j = 4 then
      begin
         let c = a2 - a1 in
            if c > 0 then S(c, "(" ^ ts2 ^ "-" ^ ts1 ^ ")", true)
            else Pas_de_sol
      end
   else if j = 5 then
      begin
         if a2 mod a1 = 0 && a1<>1 then S(a2 / a1, "(" ^ ts2 ^ "/" ^ ts1 ^ ")", true)
         else Pas_de_sol
      end
   else Pas_de_sol;;



(*La fonction "verif" v�rifie si p est r�soluble en un coup, si oui, elle fournit aussi la solution*)

let rec verif p = match p with
   | P ([], r, s) -> (Pas_de_sol, false)
   | P (_, r, []) -> (Pas_de_sol, false)
   | P (p :: q, r, sp :: sq) ->
      if p = r then (S (r, sp, true), true)
      else verif (P (q, r, sq));;



(*"resol" trouve une solution le plus rapidement possible, mais pas la meilleure, 
et seulement quand le compte bon existe, 
ce programme n'est pas fait pour �tre utilis�, il intervient dans un suivant*)

let rec resol p =
   match verif p with
   | (a, true) -> a
   | (a, false) ->
      match p with
      | P (l, r, []) -> Pas_de_sol
      | P (l, r, ps :: qs) ->
         match l with
         | [] -> Pas_de_sol
         | [a] ->
            if a < (2 * r) then S (a, ps, a = r)
            else S (0, "", false)
         | l ->
            let ltriee, striee = tri_fusion l (ps :: qs) in
               let n = max_possible (P (ltriee, r, striee)) in match n with
                  | Pas_de_sol -> n
                  | S (i0, s0, b0) -> if i0 <= r then n
                     else
                        let tab, m = tab_de_permut l in
                           let tab_s = fst (tab_de_permut (ps :: qs)) in
                              let k = ref 0 in
                                 let c = ref true in
                                    let sol = ref (Pas_de_sol) in
                                       while !k < m && !c do
                                          begin
                                             match (tab.(!k), tab_s.(!k)) with
                                             | ([], _) -> ()
                                             | ([a], _) -> ()
                                             | (_, []) -> ()
                                             | (_, [a]) -> ()
                                             | (a1 :: a2 :: q, ts1 :: ts2 :: qs1) ->
                                                begin
                                                   let j = ref 0 in
                                                      while !j <> 6 && !c do
                                                      begin
                                                         match ope a1 a2 !j ts1 ts2 with
                                                         | Pas_de_sol -> ()
                                                         | S(i1, s1, b1) ->

                                                         		match resol (P (i1 :: q, r, s1 :: qs1)) with
                                                                  | Pas_de_sol -> ()
                                                                  | S (i, s, b) ->
                                                                     if b then
                                                                        begin
                                                                           sol := S (i, s, b);
                                                                           c := false
                                                                        end
                                                               end;
                                                            j := !j + 1
                                                      done
                                                end
                                          end;
                                          k := !k + 1
                                       done;
                                       !sol;;





(*"resol_au_plus_proche" trouve une solution, qu'il y ait ou non compte bon,
quitte � parcourir toute les possibilit�s pour trouver la solution la plus proche, 
il va fournir la meilleure solution, au sens du nombre minimal de nombres utilis�s.
Ce programme n'est pas fait pour �tre utilis�, du � la forme contraignante d'un �l�ment de type partie,
il intervient dans un suivant*)

let rec resol_au_plus_proche p =
   match verif p with
   | (a, true) -> a
   | (a, false) ->
      match p with
      | P (l, r, []) -> Pas_de_sol
      | P (l, r, ps :: qs) ->
         match l with
         | [] -> Pas_de_sol
         | [a] ->
            if a < (2 * r) then S (a, ps, a = r)
            else Pas_de_sol
         | l ->
            let ltriee, striee = tri_fusion l (ps :: qs) in
               let n = max_possible (P (ltriee, r, striee)) in match n with
               		| Pas_de_sol -> n
                  | S (i0, s0, b0) -> if i0 <= r then n
                     else
                        let tab, m = tab_de_permut l in
                           let tab_s = fst (tab_de_permut (ps :: qs)) in
                              let k = ref 0 in
                                 let c = ref max_int in
                                    let w = ref max_int in
                                       let sol = ref (Pas_de_sol) in
                                          while !k < m do
                                             begin
                                                match (tab.(!k), tab_s.(!k)) with
                                                | ([], _) -> ()
                                                | ([a], _) -> ()
                                                | (_, []) -> ()
                                                | (_, [a]) -> ()
                                                | (a1 :: a2 :: q, ts1 :: ts2 :: qs1) ->
                                                   begin
                                                      for j = 0 to 5 do
                                                         match ope a1 a2 j ts1 ts2 with
                                                         | Pas_de_sol -> ()
                                                         | S(i1, s1, b1) ->
                                                         		match resol_au_plus_proche (P (i1 :: q, r, s1 :: qs1)) with
                                                         			  | Pas_de_sol -> ()
                                                                  | S (i, s, b) ->
                                                                     if s <> "" then
                                                                        let long = String.length s in
                                                                           if (long < !c && abs (i - r) = !w) || abs (i - r) < !w then
                                                                              begin
                                                                                 sol := S (i, s, b);
                                                                                 c := long;
                                                                                 w := abs (i - r)
                                                               end
                                                      done
                                                   end
                                             end;
                                             k := !k + 1
                                          done;
                                          !sol;;



(*"resol_rapide" associe � l, de la forme r::q avec r le r�sultat et q la liste 
des chiffres � utiliser :
-le r�sultat, mais seulement si le compte est bon.
(mais pas le meilleur, dans le sens ou il n'utilise pas forc�ment le moins de plaques possible)
-la fa�on de le calculer

Si le compte n'est pas bon on doit annalyser toute les possibilit�s pour trouver la plus proche du r�sultat,
ce qui n�c�ssite beaucoup de calcul, c'est pourquoi ce cas n'est pas pris en compte par ce programme "rapide"*)

let resol_rapide l = 
   match l with
   | [] -> S (0, "", false)
   | r :: q0 ->
      let rec aux q = match q with  
      (*aux cr�e la liste s, la transform�e de la liste d'entier l en liste de chaine caract�re 
      exemple : aux [10;50;3;1; 1] -> ["10";"50";"3";"1";"1"]*)
         | [] -> [""]
         | [a] -> [string_of_int a]
         | p :: q1 -> string_of_int p :: aux q1 in
         resol (P (q0, r, aux q0));;



(*"solution_chiffre_dcdl" associe � l, de la forme r::q avec r le r�sultat et q la liste 
des chiffres � utiliser :
-le r�sultat le plus proche 
(et le meilleur, dans le sens ou il utilise le moins de plaques possible)
-la fa�on de le calculer
-un bool�en qui indique si le compte est bon ou non*)

let solution_chiffre_dcdl l = 
   match l with
   | [] -> S (0, "", false)
   | r :: q0 ->
      let rec aux q = match q with  
      (*aux cr�e la liste s, la transform�e de la liste d'entier l en liste de chaine caract�re 
      exemple : aux [10;50;3;1; 1] -> ["10";"50";"3";"1";"1"]*)
         | [] -> [""]
         | [a] -> [string_of_int a]
         | p :: q1 -> string_of_int p :: aux q1 in
         resol_au_plus_proche (P (q0, r, aux q0));;



(*exemples d'utilisation *)
(*
solution_chiffre_dcdl [860;3;25;100;6;2;75];;
solution_chiffre_dcdl [807;10;50;3;1;1;7];;
solution_chiffre_dcdl [80;10;50;3;1;1;100];;
solution_chiffre_dcdl [1001;10;50;3;1;1;75];;
solution_chiffre_dcdl [1001;10;50;3;1;3;25];;
solution_chiffre_dcdl [1001;10;50;3;75;50];;
solution_chiffre_dcdl [301;9;8;1;9;5;1];;

solution_chiffre_dcdl [890;1;10;2;7;5;8];;*)


(*et certes, pas tr�s rapide, mais plus d�monstratif
resol_rapide [8579; 428;45;567;9;8;7];;*)

(* je trouve environ 1 secondes pour ce calcul, ce qui semble raisonnable par rapport � sa complexit�!
Certe on remarque qu'avec 6 plaques, il n'y a que peu de résultat qui aboutissent.
Egalement, si l'on choisit d'utiliser plus de plaques, le temps de calcul est décuplé*)

resol_rapide [91372; 172;96;268;64;4;22;78];;
(*on trouve un resultat en 17s ici*)
