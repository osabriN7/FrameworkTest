                        (********************************************)
                        (*      Projet : Infrastructure de tests    *)
                        (********************************************)  

open Delimcc

(*On definit module type Monade et on l'utilisera pour la plupart des test pour ce projet*)
module type MONADE =
sig
  type 'a t
  val map : ('a -> 'b)->('a t-> 'b t)
  val return : 'a -> 'a t
  val (>>=) : 'a t -> ('a ->'b t)->'b t
  val zero : 'a t
  val (++) : 'a t -> 'a t -> 'a t
  val uncons : 'a t ->('a *'a t) option
  val unfold  : ('b->('a*'b) option)->('b->'a t)
end

module NDIter : MONADE =
struct 
  type 'a t = Tick of ('a*'a t) option Lazy.t
  let uncons (Tick f) = Lazy.force f
  let rec map f flux  = Tick(lazy(match uncons flux with
  |None->None
  |Some(t,q) -> Some(f t,map f q )))
  let return a = Tick(lazy(Some(a,Tick(lazy(None)))))
  let rec (++) f1 f2 = Tick(lazy(match uncons f1 with
  |None->uncons f2
  |Some(t,q)->Some(t,q ++ f2)))
  let rec (>>=) flux f = Tick(lazy(match uncons flux with 
  |None->None
  |Some(t,q)->uncons(f t ++ (q>>=f))))
  let zero = Tick(lazy(None))
  let rec unfold f e =
    Tick(lazy(
      match f e with
      |None->None
      |Some(t,e')-> Some(t,unfold f e')));;
end

(* module InfraTest qui regroupe les primitives  du  sujet *)

module InfraTest =
  struct
    include NDIter
let  prompt0 = Delimcc.new_prompt ();;
(*****************************************************************************************)
(* fonction qui suit l'execution des deux fils est renvoie true si les deux sont valides *)
(* signature :                                                                           *)
(*         bool -> bool -> int -> bool                                                   *)
(* paramètres : - le resultat de l'execution fille1                                      *)
(*                - le resultat de l'execution fille2                                    *)
(*                - entier designe                                                       *)
(*                le type d'execution  forall_bool => 1 si forsome_bool =>0              *)
(* résulat  : résulat de l'execution père                                                *)
(*****************************************************************************************)
let suivre result1 result2 i = match result1,result2,i with
|true,true,_-> true
|true,_,2 -> true
|_,true,2 -> true
|_,_,_-> false
;;

(*****************************************************************************************)
(* fonction qui suit l'execution de tout les fils générés et revoie true si elles        *)
(* sont valides                                                                          *)
(*                                                                                       *)
(* signature :       bool t -> bool                                                      *)
(*                                                                                       *)
(* paramètres : - le flux qui regroupe le résultat des executions  filles                *)
(*                                                                                       *)
(* résulat  : return true si toutes les executions sont valides                          *)
(*****************************************************************************************)
let rec suivreAll flux =
  match uncons flux with
  |None-> true
  |Some(t,q)-> if not(t) then false else suivreAll q
let failure () =  if true then Delimcc.shift prompt0 (fun _->false ) else ()
;;

(*****************************************************************************************)
(* fonction qui suit l'execution de tout les fils générés et revoie true si il y a       *)
(* au moins n executions  valides                                                        *)
(*                                                                                       *)
(* signature :      int -> bool t -> bool                                                *)           
(*                                                                                       *)
(* paramètres : -  nombre d'execution à etre valide                                      *)
(*              -  le flux qui regroupe le résultat des executions  filles               *)                                                      
(* résulat  : return true au moins n  executions sont valides                            *)
(*****************************************************************************************)
let rec suivreAtleast n flux = if n = 0 then true else 
  match uncons flux with
  |None->false
  |Some(t,q)-> if t then suivreAtleast (n-1) q else suivreAtleast n q
;;

(*****************************************************************************************)
(* fonction qui "forke" l'exécution courante en deux versions.                           *)
(*L'exécution "parente" est valide ssi les deux exécutions "filles" le sont.             *)
(*                                                                                       *)
(*                                                                                       *)
(* signature :      unit -> bool                                                         *)           
(*                                                                                       *)
(* paramètres : -                                                                        *)                                                      
(* résulat  : return true      ssi les deux exécutions "filles" le sont                  *)
(*****************************************************************************************)
let forall_bool () =  Delimcc.shift prompt0 (fun k -> ((suivre  (k(true)) (k(false)) 1)));;

(*****************************************************************************************)
(* fonction qui "forke" l'exécution courante en deux versions.                           *)
(*L'exécution "parente" est valide ssi au moins une des deux exécutions est valide.      *)
(*                                                                                       *)
(*                                                                                       *)
(* signature :      unit -> bool                                                         *)           
(*                                                                                       *)
(* paramètres : -                                                                        *)                                                      
(* résulat  : return true  ssi au moins une des deux exécutions "filles" est valide      *)
(*****************************************************************************************)
let forsome_bool () = Delimcc.shift prompt0 (fun k -> (suivre (k(true))  (k(false)) 2));;

(*****************************************************************************************)
(* fonction qui "forke" l'exécution courante en deux versions en renvoyant les deuxvaleur*)
(*en paramètre                                                                           *)
(*L'exécution "parente" est valide ssi les deux exécutions "filles" le sont.             *)
(*                                                                                       *)
(*                                                                                       *)
(* signature :      'a-> 'a -> 'a                                                        *)           
(*                                                                                       *)
(* paramètres : - premiere valeur renvoyée                                               *)
(*               - deuxème valeur renvoyée                                               *)                                                      
(* résulat  : return true      ssi les deux exécutions "filles" le sont                  *)
(*****************************************************************************************)
let forall_bool_x_y (x,y) =  Delimcc.shift prompt0 (fun k -> (suivre  (k(x))  (k(y)) 1 ));;

(*****************************************************************************************)
(* fonction qui interrompt l'execution et la rend valide                                 *)
(*                                                                                       *)
(*                                                                                       *)
(*                                                                                       *)
(* signature :      unit -> unit                                                         *)           
(*                                                                                       *)
(* paramètres : -                                                                        *)
(*                                                                                       *)                                                      
(* résulat  :                                                                            *)
(*****************************************************************************************)
let miracle () =  if true then Delimcc.shift prompt0 (fun _->true ) else ();;

(*****************************************************************************************)
(* fonction qui "forke" l'exécution courante en autant de version qu'il y a d'élements   *)
(*dans le flux                                                                           *)
(*                                                                                       *)
(*                                                                                       *)
(*                                                                                       *)
(* signature :    'a t -> 'a                                                             *)           
(*                                                                                       *)
(* paramètres : - flux d'element 'a                                                      *)
(*               -                                                                       *)                                                      
(* résulat  : return true      ssi tout les éxécutions sont valides                      *)
(*****************************************************************************************)
let forall l = Delimcc.shift prompt0 (fun k ->suivreAll(map (k) l));;

(*****************************************************************************************)
(* fonction qui "forke" l'exécution courante en autant de version qu'il y a d'élements   *)
(*dans le flux                                                                           *)
(*                                                                                       *)
(*                                                                                       *)
(*                                                                                       *)
(* signature :    int->'a t -> 'a                                                        *)           
(*                                                                                       *)
(* paramètres :  -  nombre d'execution  à  valider                                       *)
(*               -  flux d'element 'a                                                    *)                                                      
(* résulat  : return true      ssi au moins n execution est valide                       *)
(*****************************************************************************************)
let foratleast n l  = Delimcc.shift prompt0 (fun k ->suivreAtleast n (map (k) l));;

(*****************************************************************************************)
(* forsome =  foratleast 1                                                               *)
(*****************************************************************************************)
let forsome l = foratleast 1 l;;

(*****************************************************************************************)
(* fonction qui filtre est ne continue  que les exécutions qui vérifient le prédicat     *)
(* en parametre                                                                          *)
(*                                                                                       *)
(*                                                                                       *)
(*                                                                                       *)
(* signature :    (unit -> bool) -> unit                                                 *)           
(*                                                                                       *)
(* paramètres :  -                                                                       *)
(*               -                                                                       *)                                                      
(* résulat  :                                                                            *)
(*****************************************************************************************)
let assumption p =  if not(p()) then Delimcc.shift prompt0 (fun _->false ) else ();;

(*****************************************************************************************)
(* fonction qui filtre est ne continue  que les exécutions qui vérifient le prédicat     *)
(* en parametre les autre sont déclaré invalide                                          *)
(*                                                                                       *)
(*                                                                                       *)
(*                                                                                       *)
(* signature :    (unit -> bool) -> unit                                                 *)           
(*                                                                                       *)
(* paramètres :                                                                          *)                                                      
(* résulat  :                                                                            *)
(*****************************************************************************************)
let assertion p =   if not(p()) then Delimcc.shift prompt0 (fun _->false) else ();;

let check  prog_int = (Delimcc.push_prompt prompt0 (fun () -> prog_int ();true));;

end


(*module Test qui test les primitives si dessous*)
module Test =
struct
  include InfraTest
 
let est_premier n =
  
let rec aux i =
      if i = n then true 
      else if n mod i = 0 then false
      else aux (i+1)
  in 
if n = 1 then false else aux 2;;
let pgcd x y =
  let rec pg x y =
    if (x mod y) = 0 then y
    else pg y (x mod y)
  in pg x y;; 

(*exemple sujet, sont exécution au sein d'un check renvoie true *)
let test_sujet1 () = let values = unfold(fun cpt ->if cpt>50 then None else Some(cpt,cpt+1)) 2 
 in let a = forall values in 
 let b = forsome values in
 assumption(fun () ->a<>b);
 let r = est_premier a in
 assertion (fun ()->r || a mod b = 0);;

 (*test de la primitive , sont exécution au sein d'un check renvoie true *)
let test_forall () = let values = unfold(fun cpt ->if cpt>10 then None else Some(cpt,cpt+1)) 1 in
                let a = forall values in assertion (fun ()->a >0)

(*deuxieme test de la primitive forall, sont exéction dans un check renvoie false car il existe dans
 le flux des valeurs négatives*)
let test_forall1 () = let values = unfold(fun cpt ->if cpt>10 then None else Some(cpt,cpt+1)) (-5) in
let a = forall values in assertion (fun ()->a >0)

(*test de la primitive forsome sont execution renvoie true car le flux passe par 0*)
let test_forsome () = let values = unfold(fun cpt ->if cpt>10 then None else Some(cpt,cpt+1)) (-10) in
let a = forsome values in assertion (fun ()->a =0)

(*test de la primitive miracle sont exécution renvoie true *)
let test_miracle () = miracle();assertion (fun ()-> false)

(*test de la primitive failure son execution  renvoie false *)
let test_failure () = failure ();assertion(fun ()->true)

(*tets des deux  primitives forxxx_bool ensemble sont execution renvoie true car il existe 
 un b sauveur de l'expression*)
let test_for_bool () = let a = forall_bool() in let  b =forsome_bool() in assertion(fun ()-> a || b)

(*deuxieme test des deux primitives renvoie false*)
let test_for_bool_2 () = let a = forall_bool() in let  b =forsome_bool() in assertion(fun ()-> a && b)
end

                          (*******************************)
                          (*         Extension 2         *)
                          (*******************************)
 
                         
(*On choisi d'implanter l'extension 2 du sujet *)
(*module QuantifList regroupe les primitive demandé pour l'extension*)
module QuantifList =
struct
  include InfraTest

(*****************************************************************************************)
(* fonction qui construit toute les liste de taille n possible  à partir d'un ensemble   *)
(*donnée                                                                                 *)
(*                                                                                       *)
(*                                                                                       *)
(*                                                                                       *)
(* signature :  int -> (unit -> 'a) -> 'a list                                           *)           
(*                                                                                       *)
(* paramètres : taille de la liste                                                       *) 
(*             - quantificateur sur les élements                                         *)                                                      
(* résulat  :                                                                            *)
(*****************************************************************************************)
  let rec construire n f =if n=0 then [] else f()::construire (n-1) f

(*****************************************************************************************)
(* fonction qui represente le quantificateur exsite                                      *)
(*                                                                                       *)
(*                                                                                       *)
(*                                                                                       *)
(*                                                                                       *)
(* signature :   int InfraTest.t -> (unit -> 'a) -> 'a list                              *)           
(*                                                                                       *)
(* paramètres : les longueurs possibles sur lesquelles on quantifie                      *) 
(*             - quatificateur sur les element de la list                                *)                                                      
(* résulat  :                                                                            *)
(*****************************************************************************************)
  let forsome_length lengths f = let n = forsome lengths in construire n f

(*****************************************************************************************)
(* fonction qui represente le quantificateur pour tout                                   *)
(*                                                                                       *)
(*                                                                                       *)
(*                                                                                       *)
(*                                                                                       *)
(* signature :   int InfraTest.t -> (unit -> 'a) -> 'a list                              *)           
(*                                                                                       *)
(* paramètres : les longueurs possibles sur lesquelles on quantifie                      *) 
(*             - quatificateur sur les element de la list                                *)                                                      
(* résulat  :                                                                            *)
(*****************************************************************************************)
  let forall_length lengths f = let n = forall lengths in construire n f

(*****************************************************************************************)
(* fonction qui represente le quantificateur pour au moins p valeurs                     *)
(*                                                                                       *)
(*                                                                                       *)
(*                                                                                       *)
(*                                                                                       *)
(* signature :   int InfraTest.t -> (unit -> 'a) -> 'a list                              *)           
(*                                                                                       *)
(* paramètres : les longueurs possibles sur lesquelles on quantifie                      *) 
(*             - quatificateur sur les element de la list                                *)                                                      
(* résulat  :                                                                            *)
(*****************************************************************************************)

  let foratleast_length p lengths f = let n = foratleast p lengths in construire n f 

end

(*On test les primitives ci dessus en utilisant l'exemple du sujet (mem ) *)
module TestQuantif =
struct
  include QuantifList
  let test_sujet () = let lengths = unfold(fun cpt -> if cpt >3 then None else Some(cpt,cpt+1)) 0 in
  let values = unfold(fun cpt -> if cpt >5 then None else Some(cpt,cpt+1)) 0 in
  let l = forall_length lengths (fun ()-> forall values) in
  let x = forall values in
  let l1 = forsome_length lengths (fun ()->forsome values) in
  let l2 = forsome_length lengths (fun ()->forsome values) in 
  let r = List.mem x l in 
  assertion (fun ()->r = (l=l1@(x::l2)))
end


(*On test également en utilisant le  dernier test du projet *)
module TestProjet =
struct
  include QuantifList
  let compare x y = if x < y then true else false
  let rec insertion e l = 
    match l with
    |[]->return [e]
    |t::q->(return(t::l) ++ insertion e q >>=(fun x -> return(t::x)))

  let rec permuation l = 
    match l with
    |[]->return []
    |t::q-> permuation q >>= insertion t

  let rec merge  l1 l2 = match l1,l2 with
  |[],_->l2
  |_,[]->l1
  |t1::q1,t2::q2 -> if compare t1  t2 then t1::(merge q1 l2) else t2::(merge l1 q2)
  (* decomposition par programmation non-deterministe *)
  (*split l renvoie toutes les decomposition possibles de 1 dans l1 et l2*)
  let split l =
    let len = List.length l in
    (*pour couper une liste en 2 à une position donnée*)
    let rec split_after l n =
      if n = 0 then ([],l) else let (l1,l2) = split_after (List.tl l) (n-1) in ((List.hd l)::l1,l2)  in
      (**les valeurs de l1 et l2 sont à choisir dans une permutaion de l*)
        forall  (permuation l >>= fun perm -> 
        let (l1,l2) = split_after perm (len/2) in
        return (l1,l2) ++ (if len mod 2 = 0 then zero else return (l2,l1)))

      let rec mergesort l =
        match l with
        |[]  |[_]->l
        |_-> let l1,l2 = split l in merge (mergesort l1) (mergesort l2)

      let prog_test_final () = let lengths = unfold(fun cpt -> if cpt >2 then None else Some(cpt,cpt+1)) 0 in
      let values = unfold(fun cpt -> if cpt >2 then None else Some(cpt,cpt+1)) 0 in
      let l = forall_length (lengths) (fun ()-> forall values ) in
      assertion (fun ()-> List.sort Pervasives.compare l = mergesort l)   
    end





