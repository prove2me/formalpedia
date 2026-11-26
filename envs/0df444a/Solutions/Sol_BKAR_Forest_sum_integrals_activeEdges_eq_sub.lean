-- Prove2me | solution 1 for BKAR.Forest.sum_integrals_activeEdges_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:35:18.346313+00:00
-- url     : https://prove2.me/submissions/d928f5f5-20b5-4b04-92ba-3227fb9c23f5

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_intervalIntegrable_activeEdgePartialSum
import Theorems.Thm_BKAR_Forest_integral_activeEdgePartialSum_eq_sum_integrals
import Theorems.Thm_BKAR_Forest_integral_activeEdgePartialSum_eq_sub

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hρ : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ ρ (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))
        MeasureTheory.volume a b) :
    Finset.sum F.activeEdges
      (fun e => ∫ t in a..b,
        partialDeriv e ρ (F.interpWithFill u t)) =
      ρ (F.interpWithFill u b) - ρ (F.interpWithFill u a) := by
  rw [← F.integral_activeEdgePartialSum_eq_sum_integrals u ρ a b hint]
  exact F.integral_activeEdgePartialSum_eq_sub u ρ a b hρ
    (F.intervalIntegrable_activeEdgePartialSum u ρ a b hint)
end BKAR.Forest
