-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.consGrowth_branchIntegral_eq_integral_tail_partialDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:19.748264+00:00
-- url     : https://prove2.me/submissions/e888f14d-b229-4fc2-990a-2fa55a14af61

import Definitions.Def_BKAR_OrderedTerminal
import Definitions.Def_BKAR_OrderedRecursion
import Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.ActiveExtension
theorem _root_.solution
    (h : ActiveExtension F e) (tail : OrderedGrowth h.forest order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (h.consGrowth tail).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (h.extension.extendParam u t)
          (partialDeriv e ρ) :=
  h.consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv tail 1 u ρ
end BKAR.Forest.ActiveExtension
