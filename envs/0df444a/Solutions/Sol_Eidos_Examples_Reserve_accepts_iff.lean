-- Prove2me | solution 1 for Eidos.Examples.Reserve.accepts_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:37:01.910087+00:00
-- url     : https://prove2.me/submissions/a1959040-fc01-442e-a368-29faa7a348ba

import Definitions.Def_Eidos_Ergo_Expr
import Definitions.Def_Eidos_Examples_Reserve
import Theorems.Thm_Eidos_Ergo_Long_ofInt_eq_ok_iff
import Theorems.Thm_Eidos_Ergo_Long_sub_eq_ok_iff
attribute [local simp] Eidos.Ergo.Long.ofInt_eq_ok_iff
attribute [local simp] Eidos.Ergo.Long.sub_eq_ok_iff



set_option autoImplicit false
open Eidos Eidos.Examples Eidos.Examples.Reserve
open Ergo
namespace Eidos.Examples.Reserve
theorem _root_.solution (reserve : Long) (ctx : Context) :
    Accepts (script reserve) ctx ↔
      ∃ out, ctx.outputs[0]? = some out ∧
        out.value.val ≤ ctx.self.value.val ∧ reserve.val ≤ out.value.val := by
  cases h : ctx.outputs with
  | nil => simp [Accepts, script, BoolExpr.eval, LongExpr.eval, Context.outputValue,
      bind, Except.bind, h]
  | cons out rest =>
      by_cases hle : out.value.val ≤ ctx.self.value.val
      · simp [Accepts, script, BoolExpr.eval, LongExpr.eval, Context.outputValue,
          bind, pure, Except.bind, Except.pure, h, hle]
      · simp [Accepts, script, BoolExpr.eval, LongExpr.eval, Context.outputValue,
          bind, pure, Except.bind, Except.pure, h, hle]
end Eidos.Examples.Reserve
