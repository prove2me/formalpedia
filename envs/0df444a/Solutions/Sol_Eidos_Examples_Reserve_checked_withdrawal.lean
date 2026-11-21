-- Prove2me | solution 1 for Eidos.Examples.Reserve.checked_withdrawal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:37:27.929968+00:00
-- url     : https://prove2.me/submissions/fe6fb534-e5d5-4e6d-a586-11930b2aeb89

import Definitions.Def_Eidos_Ergo_Expr
import Definitions.Def_Eidos_Examples_Reserve
import Theorems.Thm_Eidos_Examples_Reserve_accepts_iff
import Theorems.Thm_Eidos_Ergo_Long_sub_nonnegative


set_option autoImplicit false
open Eidos Eidos.Examples Eidos.Examples.Reserve
open Ergo
namespace Eidos.Examples.Reserve
theorem _root_.solution (reserve : Long) (ctx : Context)
    (nonnegative : 0 ≤ reserve.val) (accepted : Accepts (script reserve) ctx) :
    ∃ out amount, ctx.outputs[0]? = some out ∧
      Long.sub ctx.self.value out.value = .ok amount ∧
      0 ≤ amount.val ∧ amount.val ≤ ctx.self.value.val - reserve.val := by
  obtain ⟨out, hout, hself, hreserve⟩ := (accepts_iff reserve ctx).1 accepted
  obtain ⟨amount, hsub, hvalue, hnonneg⟩ :=
    Long.sub_nonnegative ctx.self.value out.value (by omega) hself
  exact ⟨out, amount, hout, hsub, hnonneg, by omega⟩
end Eidos.Examples.Reserve
