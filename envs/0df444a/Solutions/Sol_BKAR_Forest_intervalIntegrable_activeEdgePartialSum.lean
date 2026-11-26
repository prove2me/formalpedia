-- Prove2me | solution 1 for BKAR.Forest.intervalIntegrable_activeEdgePartialSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:06.274051+00:00
-- url     : https://prove2.me/submissions/bfeb7e2f-8fcb-47ee-bf58-0e3bc9bd6f66

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_activeEdgePartialSum_def


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))
        MeasureTheory.volume a b) :
    IntervalIntegrable (fun t : ℝ => F.activeEdgePartialSum u ρ t)
      MeasureTheory.volume a b := by
  refine (IntervalIntegrable.sum F.activeEdges
      (f := fun e t => partialDeriv e ρ (F.interpWithFill u t))
      hint).congr ?_
  intro t _
  change (∑ e ∈ F.activeEdges,
      (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))) t =
    F.activeEdgePartialSum u ρ t
  rw [F.activeEdgePartialSum_def u ρ t, Finset.sum_apply]
end BKAR.Forest
