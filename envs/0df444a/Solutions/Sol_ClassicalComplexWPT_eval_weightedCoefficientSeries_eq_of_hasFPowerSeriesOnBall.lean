-- Prove2me | solution 1 for ClassicalComplexWPT.eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesOnBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:13:07.824224+00:00
-- url     : https://prove2.me/submissions/cb253a7b-fef5-4cce-af45-2f1a67fe25b1

import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Theorems.Thm_ClassicalComplexWPT_eval_weightedCoefficientSeries_eq
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply



set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    {f : Ambient n → ℂ} (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (r : ℝ≥0) {ρ : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p 0 ρ)
    (hr0 : 0 < r) (hrp : (r : ℝ≥0∞) < p.radius)
    (z : Base n) (w : ℂ)
    (hzq : z ∈ Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius)
    (hzw : (‖(z, (0 : ℂ))‖₊ + ‖((0 : Base n), w)‖₊ : ℝ≥0∞) < ρ)
    (hw : ‖w‖ < r) :
    evalL1PowerSeries ((weightedCoefficientSeries p r).sum z) ((r : ℂ)⁻¹ * w) =
      f (z, w) := by
  rw [eval_weightedCoefficientSeries_eq p r hr0 hrp z w hzq
    (hzw.trans_le hp.r_le) hw]
  symm
  have hball : (z, w) ∈ Metric.eball (0 : Ambient n) ρ := by
    rw [mem_eball_zero_iff]
    have hpair : (‖(z, w)‖₊ : ℝ≥0∞) ≤
      ‖(z, (0 : ℂ))‖₊ + ‖((0 : Base n), w)‖₊ := by
      rw [show (z, w) = (z, (0 : ℂ)) + ((0 : Base n), w) by ext <;> simp]
      exact_mod_cast nnnorm_add_le (z, (0 : ℂ)) ((0 : Base n), w)
    exact hpair.trans_lt hzw
  simpa only [zero_add] using hp.sum hball
end ClassicalComplexWPT
