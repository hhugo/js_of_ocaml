(* Js_of_ocaml compiler
 * http://www.ocsigen.org/js_of_ocaml/
 * Copyright (C) 2010 Jérôme Vouillon
 * Laboratoire PPS - CNRS Université Paris Diderot
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, with linking exception;
 * either version 2.1 of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *)
open! Stdlib
open Code
open Flow

let rec function_cardinality info x acc =
  get_approx
    info
    (fun x ->
      match info.info_defs.(Var.idx x) with
      | Expr (Closure (l, _)) -> Some (List.length l)
      | Expr (Prim (Extern "%closure", [ Pc (IString prim) ])) -> (
          try Some (Primitive.arity prim) with Not_found -> None)
      | Expr (Apply (f, l, _)) -> (
          if List.mem f ~set:acc
          then None
          else
            match function_cardinality info f (f :: acc) with
            | Some n ->
                let diff = n - List.length l in
                if diff > 0 then Some diff else None
            | None -> None)
      | _ -> None)
    None
    (fun u v ->
      match u, v with
      | Some n, Some m when n = m -> u
      | _ -> None)
    x

let specialize_instr info (acc, free_pc, extra) i =
  match i with
  | Let (x, Apply (f, l, _)) when Config.Flag.optcall () -> (
      let n' = List.length l in
      match function_cardinality info f [] with
      | None -> i :: acc, free_pc, extra
      | Some n when n = n' -> Let (x, Apply (f, l, true)) :: acc, free_pc, extra
      | Some n when n < n' ->
          let v = Code.Var.fresh () in
          let args, rest = Stdlib.List.take n l in
          ( Let (v, Apply (f, args, true)) :: Let (x, Apply (v, rest, false)) :: acc
          , free_pc
          , extra )
      | Some n when n > n' ->
          let missing = Array.init (n - n') ~f:(fun _ -> Code.Var.fresh ()) in
          let missing = Array.to_list missing in
          let block =
            let params' = Array.init (n - n') ~f:(fun _ -> Code.Var.fresh ()) in
            let params' = Array.to_list params' in
            let return' = Code.Var.fresh () in
            { params = params'
            ; body = [ Let (return', Apply (f, l @ params', true)) ]
            ; branch = Return return'
            ; handler = None
            }
          in
          ( Let (x, Closure (missing, (free_pc, missing))) :: acc
          , free_pc + 1
          , (free_pc, block) :: extra )
      | _ -> i :: acc, free_pc, extra)
  | _ -> i :: acc, free_pc, extra

let specialize_instrs info p =
  let blocks, free_pc =
    Addr.Map.fold
      (fun pc block (blocks, free_pc) ->
        let body, free_pc, extra =
          List.fold_right block.body ~init:([], free_pc, []) ~f:(fun i acc ->
              specialize_instr info acc i)
        in
        let blocks =
          List.fold_left extra ~init:blocks ~f:(fun blocks (pc, b) ->
              Addr.Map.add pc b blocks)
        in
        Addr.Map.add pc { block with Code.body } blocks, free_pc)
      p.blocks
      (Addr.Map.empty, p.free_pc)
  in
  { p with blocks; free_pc }

let f info p = specialize_instrs info p

let wrap_fun =
  let step1 info { blocks; _ } =
    Addr.Map.fold
      (fun pc block (blocks, closures) ->
        let body_rev, closures =
          List.fold_left block.body ~init:([], closures) ~f:(fun (acc, closures) i ->
              match i with
              | Let (x, Closure (l, _cont)) when info.info_possibly_mutable.(Var.idx x) ->
                  let x' = Var.fork x in
                  ( Let
                      ( x'
                      , Prim
                          ( Extern "%with_arity"
                          , [ Pv x; Pc (Int (Int32.of_int (List.length l))) ] ) )
                    :: i
                    :: acc
                  , Var.Map.add x x' closures )
              | _ -> i :: acc, closures)
        in
        let blocks = Addr.Map.add pc { block with body = List.rev body_rev } blocks in
        blocks, closures)
      blocks
      (blocks, Var.Map.empty)
  in
  let f info p =
    let blocks, funs = step1 info p in
    let subst x =
      match Var.Map.find x funs with
      | exception Not_found -> x
      | y -> y
    in
    let subst_prim = function
      | Pc _ as x -> x
      | Pv x -> Pv (subst x)
    in
    let blocks =
      Addr.Map.map
        (fun block ->
          let body =
            List.map block.body ~f:(function
                | Let (x, expr) ->
                    let expr =
                      match expr with
                      | Apply (f, args, false) -> Apply (f, List.map args ~f:subst, false)
                      | Block (i, vars, e) when false ->
                          (* This is wrong as function_cardinality can see through block *)
                          Block (i, Array.map vars ~f:subst, e)
                      | Block _ -> expr
                      | Prim (Extern "%with_arity", _) as i -> i
                      | Prim (p, args) -> Prim (p, List.map args ~f:subst_prim)
                      | (Constant _ | Field _ | Closure _ | Apply (_, _, true)) as e -> e
                    in
                    Let (x, expr)
                | i -> i)
          in

          { block with body })
        blocks
    in
    { p with blocks }
  in
  f
