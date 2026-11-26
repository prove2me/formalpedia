-- Prove2me | solution 1 for ClassicalComplexWPT.le_radius_weightedCoefficientSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:07:17.312367+00:00
-- url     : https://prove2.me/submissions/6a3f376e-5b3f-4740-9aca-65fce27821b8

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_nnnorm_weightedCoefficientSeries_le
import Theorems.Thm_ClassicalComplexWPT_summable_changeOrigin_weighted_majorant
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero



set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (s r : ℝ≥0)
    (hsr : (s + r : ℝ≥0∞) < p.radius) :
    (s : ℝ≥0∞) ≤ (weightedCoefficientSeries p r).radius := by
  have hr : (r : ℝ≥0∞) < p.radius :=
    (show (r : ℝ≥0∞) ≤ s + r by simp).trans_lt hsr
  apply FormalMultilinearSeries.le_radius_of_summable_nnnorm
  refine NNReal.summable_of_le (fun l ↦ ?_)
    (summable_changeOrigin_weighted_majorant p s r hsr)
  gcongr
  exact nnnorm_weightedCoefficientSeries_le p r hr l
end ClassicalComplexWPT
