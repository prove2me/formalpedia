-- Prove2me | solution 1 for ClassicalComplexWPT.norm_evalLast_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:59:56.985047+00:00
-- url     : https://prove2.me/submissions/7f8b1118-117e-4997-a129-e319051e7018

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero



set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution (n k : ℕ) : ‖evalLast n k‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound (evalLast n k) (by norm_num) (fun q ↦ by
    simpa [evalLast, norm_lastDirection] using
      q.le_opNorm (fun _ ↦ lastDirection n))
end ClassicalComplexWPT
