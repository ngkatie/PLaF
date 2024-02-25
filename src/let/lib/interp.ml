(*
 * Name(s): Kent Quach, Katie Ng
 * Pledge: I pledge my honor that I have abided by the Stevens Honor System. 
 *)

 open Parser_plaf.Ast
 open Parser_plaf.Parser
 open Ds
     
 (** [eval_expr e] evaluates expression [e] *)
 let rec eval_expr : expr -> exp_val ea_result =
   fun e ->
   match e with
   | Int(n) ->
     return (NumVal n)
   | Var(id) ->
     apply_env id
   | Add(e1,e2) ->
     eval_expr e1 >>=
     int_of_numVal >>= fun n1 ->
     eval_expr e2 >>=
     int_of_numVal >>= fun n2 ->
     return (NumVal (n1+n2))
   | Sub(e1,e2) ->
     eval_expr e1 >>=
     int_of_numVal >>= fun n1 ->
     eval_expr e2 >>=
     int_of_numVal >>= fun n2 ->
     return (NumVal (n1-n2))
   | Mul(e1,e2) ->
     eval_expr e1 >>=
     int_of_numVal >>= fun n1 ->
     eval_expr e2 >>=
     int_of_numVal >>= fun n2 ->
     return (NumVal (n1*n2))
   | Div(e1,e2) ->
     eval_expr e1 >>=
     int_of_numVal >>= fun n1 ->
     eval_expr e2 >>=
     int_of_numVal >>= fun n2 ->
     if n2==0
     then error "Division by zero"
     else return (NumVal (n1/n2))
   | Let(id,def,body) ->
     eval_expr def >>= 
     extend_env id >>+
     eval_expr body 
   | ITE(e1,e2,e3) ->
     eval_expr e1 >>=
     bool_of_boolVal >>= fun b ->
     if b 
     then eval_expr e2
     else eval_expr e3
   | IsZero(e) ->
     eval_expr e >>=
     int_of_numVal >>= fun n ->
     return (BoolVal (n = 0))
   | Pair(e1,e2) ->
     eval_expr e1 >>= fun ev1 ->
     eval_expr e2 >>= fun ev2 ->
     return (PairVal(ev1,ev2))
   | Fst(e) ->
     eval_expr e >>=
     pair_of_pairVal >>= fun (l,_) ->
     return l
   | Snd(e) ->
     eval_expr e >>=
     pair_of_pairVal >>= fun (_,r) ->
     return r
   | Debug(_e) ->
     string_of_env >>= fun str ->
     print_endline str; 
     error "Debug called"
   (* Returns a boolean indicating whether the e is an empty binary tree *)
   | IsEmpty(e) ->
     eval_expr e >>= fun b ->
     return (BoolVal(b == TreeVal(Empty)))
   (* Creates an empty tree *)
   | EmptyTree(_t) ->
     return (TreeVal(Empty))
   (* Creates a new tree with data e1 and left and right subtrees e2 and e3 *)
   | Node(e1,e2,e3) ->
     eval_expr e1 >>= fun ev1 ->
     eval_expr e2 >>=
     tree_of_treeVal >>= fun ev2 ->
     eval_expr e3 >>=
     tree_of_treeVal >>= fun ev3 ->
     return (TreeVal(Node(ev1,ev2,ev3)))
   (* caseT e1 of { emptytree() -> e2, node(id1,id2,id3) -> e3 } *)
   | CaseT(e1,e2,id1,id2,id3,e3) ->
     eval_expr e1 >>= fun ev1 -> (
     match ev1 with
     | TreeVal(Empty) ->
       eval_expr e2
     | TreeVal(Node(d,l,r)) ->
       extend_env_list [id1;id2;id3] [d;TreeVal(l);TreeVal(r)] >>+
       eval_expr e3
     )
   (* Creates a record with n fields. Fields i is assigned the expressed value
     resulting from resulting expression ei. *)
   | Record(fs) ->
     sequence (List.map eval_expr (snd (List.split (snd (List.split fs))))) >>= fun l ->
     if has_duplicates (List.map fst fs)
       then error "Record: duplicate fields"
     else return (RecordVal (List.combine (fst (List.split fs)) l))
   (* Projects field id from the record resulting from evaluating e *)
   | Proj(e,id) ->
     eval_expr e >>=
     fields_of_recordVal >>= fun fields -> (
     match (List.assoc_opt id fields) with
       | Some value -> return value
       | _ -> error "Proj: field does not exist"
     )
 and
   eval_exprs : expr list -> (exp_val list) ea_result  =
   fun es ->
   match es with
   | [] -> return []
   | h::t -> eval_expr h >>= fun i ->
     eval_exprs t >>= fun l ->
     return (i::l)
   | _ -> failwith "Not implemented yet!"
 
 (** [eval_prog e] evaluates program [e] *)
 let eval_prog (AProg(_,e)) =
   eval_expr e
 
 
 (** [interp s] parses [s] and then evaluates it *)
 let interp (e:string) : exp_val result =
   let c = e |> parse |> eval_prog
   in run c
 