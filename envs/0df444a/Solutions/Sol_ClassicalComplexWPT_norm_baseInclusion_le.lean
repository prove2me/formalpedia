-- Prove2me | solution 1 for ClassicalComplexWPT.norm_baseInclusion_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:59:56.424945+00:00
-- url     : https://prove2.me/submissions/50192475-a6a4-46e4-ae96-a8615e79aa98

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
theorem _root_.solution (n : ℕ) : ‖baseInclusion n‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound (baseInclusion n) (by norm_num) (fun z ↦ by
    simp [baseInclusion])
end ClassicalComplexWPT
