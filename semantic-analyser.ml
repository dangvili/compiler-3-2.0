(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let create_bound_env _vars=
    let rec helper index lst = 
        match lst with
            | [] -> []
            | [_var] -> [Var'(VarBound(_var , 0 , index))]
            | car :: cdr -> [Var'(VarBound(car , 0 , index))] @ (helper (index+1) cdr) in
        (helper 0 _vars);;

let extend_bound_vars _bound_vars =
    let rec helper _vars=
        match _vars with
            |Var'(VarBound(_var , _majorIdx , _minorIdx)) -> Var'(VarBound(_var , (_majorIdx+1) , _minorIdx))
            | _ ->raise X_syntax_error in
        (helper _bound_vars);;
            
let get_var_param _var _params = 
    let rec helper _params _index = 
        match _params with
        | [] -> Const'(Sexpr(Nil))
        |  car :: cdr ->
            if((compare car _var) == 0)
                then Var'(VarParam(_var , _index))
                else (helper cdr (_index+1)) in
        (helper _params 0);;
        
let get_var_bound _var _bound =
    let rec helper _bounds = 
        match _bounds with
        | [] -> Const'(Sexpr(Nil))
        | Var'(VarBound(_var_name , _majorIdx , _minorIdx)) :: cdr ->
            if((compare _var _var_name) == 0)
                then Var'(VarBound(_var_name , _majorIdx , _minorIdx))
                else (helper cdr) 
        | _ -> raise X_syntax_error in
        (helper _bound);;
    
let annotate_var _var _params _bound = 
    let var_param = (get_var_param _var _params) in
        if(not (expr'_eq var_param (Const'(Sexpr(Nil)))))
            then var_param
            else let var_bound = (get_var_bound _var _bound) in
                if(not (expr'_eq var_bound (Const'(Sexpr(Nil)))))
                    then var_bound 
                    else Var'(VarFree(_var));;
                    
let rec annotate e _params _bound= 
    let annotate_expr _expr = (annotate _expr _params _bound) in
        match e with
        | Const(_c) -> Const' (_c)
        | Var(_v) -> (annotate_var _v _params _bound)
        | If(_test , _then , _else) -> If' ((annotate_expr _test) , (annotate_expr _then) , (annotate_expr _else))
        | Seq(_l) -> Seq'(List.map annotate_expr _l)
        | Set(_var , _val) -> Set'((annotate_expr _var) , (annotate_expr _val))
        | Def(_var , _val) -> Def'((annotate_expr _var) , (annotate_expr _val))
        | Or(_l) -> Or'(List.map annotate_expr _l);
        | Applic(_e , _args) -> Applic'((annotate_expr _e) , (List.map annotate_expr _args))
        | LambdaSimple(_vars , _body) -> LambdaSimple'(_vars , (annotate _body _vars ((create_bound_env _params) @ (List.map extend_bound_vars _bound))))
        | LambdaOpt(_vars , _opt , _body) -> LambdaOpt'(_vars , _opt , (annotate _body (_vars @ [_opt]) ((create_bound_env _params) @ (List.map extend_bound_vars _bound))));;
                                                            
let annotate_lexical_addresses e = (annotate e [] []);;

let get_last lst = 
  let reversed = (List.rev lst) in
  let last = (List.hd reversed) in
  let rest = (List.rev (List.tl reversed)) in
  (last, rest);;

let rec aux_param_annotate_tail_calls e in_tp = 
  match e with
        | Const'(c) -> Const'(c)
        | Var'(var) -> Var'(var)
        | If' (test ,conseq , alt) -> If' ((aux_param_annotate_tail_calls test false) ,(aux_param_annotate_tail_calls conseq in_tp) ,(aux_param_annotate_tail_calls alt in_tp))
        | Seq' (exps) ->  Seq'(sequence_handler exps in_tp) (*CHANGE seqOrHandler *)
        | Set' (_var, _val) -> Set' ((aux_param_annotate_tail_calls _var false), (aux_param_annotate_tail_calls _val false))
        | Def' (_var, _val) -> Def' ((aux_param_annotate_tail_calls _var false), (aux_param_annotate_tail_calls _val false))
        | Or' (exps) -> Or' (or_handler exps in_tp)
        | LambdaSimple' (vars, body) -> LambdaSimple' (vars, (aux_param_annotate_tail_calls body true))
        | LambdaOpt' (vars, opt ,body) -> LambdaOpt' (vars, opt, (aux_param_annotate_tail_calls body true))
        | Applic' (e, args) -> (app_handler e args in_tp)(*CHANGE applicHandler*)
        | _ -> raise X_syntax_error

  and sequence_handler exps in_tp = 
    let (l, r) = get_last exps in
        (List.map hp r) @ [(aux_param_annotate_tail_calls l in_tp)]

  and or_handler exps in_tp = 
    let (l, r) = get_last exps in
        (List.map hp r) @ [(aux_param_annotate_tail_calls l in_tp)]

  and app_handler e args in_tp =
   match in_tp with
        | true -> ApplicTP'((hp e),(List.map hp args))
        | false -> Applic'((hp e),(List.map hp args))

   and hp exp = aux_param_annotate_tail_calls exp false;;

let annotate_tail_calls e = aux_param_annotate_tail_calls e false;;










let box_set e = raise X_not_yet_implemented;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
