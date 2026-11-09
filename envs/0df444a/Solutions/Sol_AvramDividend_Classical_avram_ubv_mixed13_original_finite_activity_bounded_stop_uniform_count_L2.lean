-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_bounded_stop_uniform_count_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T01:15:36.45757+00:00
-- url     : https://prove2.me/submissions/131c6497-793c-4c66-b8d1-14e56efd4077

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_square_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original finite-activity physical negative-jump count has a uniform
quadratic expectation budget at every bounded random stopping horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let R : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
    Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
      (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ R ^ 2 + R := by
  intro K R
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  have hMom :=
    avram_p4_s3_original_bounded_stop_negative_band_square_budget
      X T n τ hτ hKmeas
  change Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
      (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ r ^ 2 + r at hMom
  have hB : B ⊆ Iio (0 : ℝ) := by
    intro z hz
    have hdenom : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hfrac : (0 : ℝ) < 1 / ((n : ℝ) + 1) :=
      one_div_pos.mpr hdenom
    exact lt_of_le_of_lt hz (neg_lt_zero.mpr hfrac)
  have hTop : (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hFinite
  have hProduct :
      (T : ℝ≥0∞) * X.ν B ≤
        (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    gcongr
  have hRate : r ≤ R := ENNReal.toReal_mono hTop hProduct
  have hBound : r ^ 2 + r ≤ R ^ 2 + R := by
    gcongr
  exact ⟨hMom.1, le_trans hMom.2 hBound⟩
