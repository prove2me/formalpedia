-- Prove2me | solution 1 for Eidos.Ergo.error_not_accepted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:37:03.489757+00:00
-- url     : https://prove2.me/submissions/cec94d27-956a-4985-a3ae-53f91dc93dc0

import Definitions.Def_Eidos_Ergo_Context
import Definitions.Def_Eidos_Ergo_Expr
import Theorems.Thm_Eidos_Ergo_Long_ofInt_eq_ok_iff
import Theorems.Thm_Eidos_Ergo_Long_sub_eq_ok_iff
attribute [local simp] Eidos.Ergo.Long.ofInt_eq_ok_iff
attribute [local simp] Eidos.Ergo.Long.sub_eq_ok_iff



set_option autoImplicit false
open Eidos Eidos.Ergo
namespace Eidos.Ergo
theorem _root_.solution (script : BoolExpr) (ctx : Context) (err : EvalError)
    (h : script.eval ctx = .error err) : ¬ Accepts script ctx := by
  simp [Accepts, h]
end Eidos.Ergo
