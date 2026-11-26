-- Prove2me | solution 1 for FourierJacobi.Analysis.i0_four_rows_absolutelySummable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:20:56.37232+00:00
-- url     : https://prove2.me/submissions/c278c16b-9425-4dc5-a853-e213b78b7716

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Theorems.Thm_FourierJacobi_Analysis_i0_case1_reindexed
import Theorems.Thm_FourierJacobi_Analysis_i0_case2_reindexed
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_three_geometric
import Theorems.Thm_FourierJacobi_Analysis_i0_case6_reindexed
import Theorems.Thm_FourierJacobi_Analysis_i0_case7_reindexed

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I0PositiveRow false => ‖i0Shell t d U V T p.val‖) ∧
    Summable (fun p : I0PositiveRow true => ‖i0Shell t d U V T p.val‖) ∧
    Summable (fun p : I0NegativeRow false => ‖i0Shell t d U V T p.val‖) ∧
    Summable (fun p : I0NegativeRow true => ‖i0Shell t d U V T p.val‖) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (i0PositiveRowEquiv false).summable_iff.mp
    convert summable_norm_three_geometric ((1 - t ^ 2) ^ 2)
      (d * T * V * t) (t ^ 2) (t ^ 2) hP ht ht using 1
    exact funext fun n => congrArg norm (i0_case1_reindexed t d U V T n)
  · apply (i0PositiveRowEquiv true).summable_iff.mp
    convert summable_norm_three_geometric ((1 - t ^ 2) ^ 2 * (T * U * t ^ 4))
      (d * T * V * t) (t ^ 2) (T * U * t ^ 4) hP ht hG using 1
    exact funext fun n => congrArg norm (i0_case2_reindexed t d U V T n)
  · apply (i0NegativeRowEquiv false).summable_iff.mp
    convert summable_norm_three_geometric ((1 - t ^ 2) ^ 2 * (T * V * t / d))
      (T * V * t / d) (t ^ 2) (t ^ 2) hN ht ht using 1
    exact funext fun n => congrArg norm (i0_case6_reindexed t d U V T n)
  · apply (i0NegativeRowEquiv true).summable_iff.mp
    convert summable_norm_three_geometric
      ((1 - t ^ 2) ^ 2 * (T * V * t / d) * (T * U * t ^ 4))
      (T * V * t / d) (t ^ 2) (T * U * t ^ 4) hN ht hG using 1
    exact funext fun n => congrArg norm (i0_case7_reindexed t d U V T n)
end FourierJacobi.Analysis
