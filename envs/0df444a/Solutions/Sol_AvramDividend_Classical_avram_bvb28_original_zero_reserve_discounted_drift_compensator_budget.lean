-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb28_original_zero_reserve_discounted_drift_compensator_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:59:28.026341+00:00
-- url     : https://prove2.me/submissions/43ad0edb-3e92-4fc6-81fe-5568da2b9289

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
import Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_discounted_zero_contact_budget_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hq : 0 < q) (T : ℝ) (hT : 0 ≤ T) :
    X.drift * (∫ t in (0 : ℝ)..T, Real.exp ((-q) * t)) +
      Real.exp ((-q) * T) * w 0 ≤
    w 0 -
      (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν) *
        (∫ t in (0 : ℝ)..T, Real.exp ((-q) * t))  := by
  let I : ℝ := ∫ t in (0 : ℝ)..T, Real.exp ((-q) * t)
  let K : ℝ := ∫ z in Iio (0 : ℝ),
    w ((0 : ℝ) + z) - w 0 ∂X.ν
  have hSign : X.drift - q * w 0 + K ≤ 0 := by
    exact avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
      X hX hBV hFinite q w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad
  have hIntegral :
      q * I + Real.exp ((-q) * T) = 1 :=
    avram_bvb23_original_discounted_zero_contact_budget_identity q T hq hT
  have hExp : Real.exp ((-q) * T) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hq.le hT]
  have hINonneg : 0 ≤ I := by
    nlinarith
  have hProduct : (X.drift - q * w 0 + K) * I ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hSign hINonneg
  change X.drift * I + Real.exp ((-q) * T) * w 0 ≤
    w 0 - K * I
  nlinarith
