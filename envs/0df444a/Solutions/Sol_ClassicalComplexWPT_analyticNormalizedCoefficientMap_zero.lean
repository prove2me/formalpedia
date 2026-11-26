-- Prove2me | solution 1 for ClassicalComplexWPT.analyticNormalizedCoefficientMap_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:42.515996+00:00
-- url     : https://prove2.me/submissions/96945bde-9f2d-40a5-842e-d00e8eef6b6b

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_normalizedOriginCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_ambient_zero_eq
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_radius_weightedCoefficientSeries_pos
import Theorems.Thm_ClassicalComplexWPT_weightedCoefficientSeries_sum_apply_lastTaylorCoefficient
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply


attribute [local simp] ClassicalComplexWPT.originWeightedCoeffs_apply
attribute [local simp] ClassicalComplexWPT.normalizedOriginCoeffs_apply

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) :
    analyticNormalizedCoefficientMap p r hr d 0 = normalizedOriginCoeffs p r hr d := by
  have hzq : (0 : Base n) ∈
      Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius := by
    simpa only [Metric.mem_eball, edist_self] using
      radius_weightedCoefficientSeries_pos p r hr
  have hzp : ((0 : Base n), (0 : ℂ)) ∈
      Metric.eball (0 : Ambient n) p.radius := by
    rw [← ambient_zero_eq n]
    have hp0 : (0 : ℝ≥0∞) < p.radius :=
      (show (0 : ℝ≥0∞) ≤ r by simp).trans_lt hr
    simpa only [Metric.mem_eball, edist_self] using hp0
  have hC0 : (weightedCoefficientSeries p r).sum (0 : Base n) =
      originWeightedCoeffs p r hr := by
    apply lp.ext
    funext k
    exact weightedCoefficientSeries_sum_apply_lastTaylorCoefficient
      p r 0 k hr hzq hzp
  unfold analyticNormalizedCoefficientMap normalizedCoefficientMap normalizedOriginCoeffs
  rw [hC0]
end ClassicalComplexWPT
