-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb23_original_finite_grid_closed_lower_interior_generator_sum_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:23:16.139208+00:00
-- url     : https://prove2.me/submissions/7aa04fa2-4877-49f7-ad75-4bb44cd41b95

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (u : ℕ → ℝ≥0) (Z : ℕ → ℝ) (n : ℕ)
    (hmono : ∀ i, i < n + 1 → u i ≤ u (i + 1))
    (hZ : ∀ i, 0 ≤ Z i ∧ ENNReal.ofReal (Z i) < C) :
    (∑ i ∈ Finset.range (n + 1),
      Real.exp (-(q * (u i : ℝ))) *
      (if Z i = 0 then
        X.drift - q * w 0 +
          (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν)
       else X.generator w (Z i) - q * w (Z i)) *
      ((u (i + 1) : ℝ) - (u i : ℝ))) ≤ 0  := by
  have hboundary :=
    avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
      X hX hBV hFinite q w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
  apply Finset.sum_nonpos
  intro i hi
  have hwidth : (0 : ℝ) ≤ (u (i + 1) : ℝ) - u i := by
    exact sub_nonneg.mpr (by exact_mod_cast hmono i (Finset.mem_range.mp hi))
  have he : 0 ≤ Real.exp (-(q * (u i : ℝ))) := (Real.exp_pos _).le
  have hg :
      (if Z i = 0 then
         X.drift - q * w 0 +
           (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν)
       else X.generator w (Z i) - q * w (Z i)) ≤ 0 := by
    by_cases hz : Z i = 0
    · simpa only [hz, if_pos] using hboundary
    · have hpos : 0 < Z i := lt_of_le_of_ne (hZ i).1 (Ne.symm hz)
      simpa only [if_neg hz] using (hw_gen (Z i) hpos (hZ i).2).2
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos he hg) hwidth
