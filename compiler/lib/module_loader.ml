open! Stdlib
open Code

let js_module = true

let load_global gdata x name =
  if js_module
  then
    Let (x, Prim (Extern "%get_global", [Pv gdata; Pc (IString name)]))
  else
    Let (x, Prim (Extern "caml_js_get", [Pv gdata; Pc (IString name)]))
