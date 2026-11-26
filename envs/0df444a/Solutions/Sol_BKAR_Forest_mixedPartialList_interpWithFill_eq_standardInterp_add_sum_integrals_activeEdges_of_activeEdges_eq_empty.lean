-- Prove2me | solution 1 for BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:11.873344+00:00
-- url     : https://prove2.me/submissions/517dea1a-8587-4930-b903-b93cfaa28a82

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
import Theorems.Thm_BKAR_Forest_sum_integrals_activeEdges_mixedPartialList_eq_zero_of_activeEdges_eq_empty

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) (hF : F.activeEdges = ∅) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        Finset.sum F.activeEdges
          (fun e => ∫ t in 0..b,
            mixedPartialList (e :: es) ρ (F.interpWithFill u t)) := by
  rw [F.mixedPartialList_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
    es u ρ b hF]
  rw [F.sum_integrals_activeEdges_mixedPartialList_eq_zero_of_activeEdges_eq_empty
    es u ρ 0 b hF]
  rw [add_zero]
end BKAR.Forest
