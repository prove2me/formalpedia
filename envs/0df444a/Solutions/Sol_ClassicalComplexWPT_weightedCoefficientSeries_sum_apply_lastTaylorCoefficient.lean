-- Prove2me | solution 1 for ClassicalComplexWPT.weightedCoefficientSeries_sum_apply_lastTaylorCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:02.267334+00:00
-- url     : https://prove2.me/submissions/7162a7e5-8998-44b6-bd65-4ce7ca710219

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_weightedCoefficientSeries_sum_apply
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
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (z : Base n) (j : ℕ)
    (hr : (r : ℝ≥0∞) < p.radius)
    (hzq : z ∈ Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius)
    (hzp : (z, 0) ∈ Metric.eball (0 : Ambient n) p.radius) :
    (weightedCoefficientSeries p r).sum z j =
      (r : ℂ) ^ j * lastTaylorCoefficient p j z := by
  simpa [lastTaylorCoefficient] using
    weightedCoefficientSeries_sum_apply p r z j hr hzq hzp
end ClassicalComplexWPT
