-- Prove2me | solution 1 for FriedCrossing.OrderCount.order_zero_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:55:14.59382+00:00
-- url     : https://prove2.me/submissions/b2d8cd49-31ae-4fca-b9d6-95955641ed18

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
import Theorems.Thm_FriedCrossing_OrderCount_finrank_middle_of_exact
import Theorems.Thm_FriedCrossing_OrderCount_zetaOrder_eq

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.OrderCount
variable {K : Type*} [Field K] {V₁ V₂ V₃ : Type*}
  [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
  [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
  [AddCommGroup V₃] [Module K V₃]
namespace FriedCrossing.OrderCount
theorem _root_.solution (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃)
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g) (c : Fin 5 → ℕ) (hacyc : c 0 = 0 ∧ c 4 = 0)
    (hdual : c 3 = c 1)
    (hdims : c 1 = Module.finrank K V₁ ∧ c 2 = Module.finrank K V₂ ∧
      c 3 = Module.finrank K V₃) :
    zetaOrder c = 0 := by
  have hmid := finrank_middle_of_exact f g hf hfg hg
  rw [zetaOrder_eq c hacyc.1 hacyc.2 hdual, hdims.2.1, hdims.1]
  have h31 : Module.finrank K V₃ = Module.finrank K V₁ := by
    rw [← hdims.2.2, ← hdims.1, hdual]
  rw [hmid, h31]
  push_cast
  ring
end FriedCrossing.OrderCount
