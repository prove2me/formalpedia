-- Prove2me | solution 1 for ClassicalComplexWPT.originWeightedCoeffs_top_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:06:49.947103+00:00
-- url     : https://prove2.me/submissions/18c84ca5-a8e5-4ba3-a0a5-b8ae1b3f2ae7

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_exactOrderInLastVariable_iff_lastTaylorCoefficients
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply


attribute [local simp] ClassicalComplexWPT.originWeightedCoeffs_apply

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) (R : ℝ≥0) (hR0 : 0 < R)
    (hR : (R : ℝ≥0∞) < p.radius) :
    originWeightedCoeffs p R hR d ≠ 0 := by
  rw [originWeightedCoeffs_apply]
  have hRC : (R : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, NNReal.coe_eq_zero]
    exact hR0.ne'
  exact mul_ne_zero (pow_ne_zero _ hRC)
    ((exactOrderInLastVariable_iff_lastTaylorCoefficients p hp).mp horder).2
end ClassicalComplexWPT
