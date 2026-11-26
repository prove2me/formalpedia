-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:42:19.88858+00:00
-- url     : https://prove2.me/submissions/97f783be-1892-4623-9671-fa16391ebcea

import Definitions.Def_BKAR_OrderedTerminal
import Definitions.Def_BKAR_OrderedRecursion
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_cons_eq_integral_tail_partialDeriv
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
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (h.consGrowth tail).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        tail.branchIntegralAux t (h.extension.extendParam u t)
          (partialDeriv e ρ) :=
  OrderedGrowth.branchIntegralAux_cons_eq_integral_tail_partialDeriv
    h.extension tail top u ρ
end BKAR.Forest.ActiveExtension
