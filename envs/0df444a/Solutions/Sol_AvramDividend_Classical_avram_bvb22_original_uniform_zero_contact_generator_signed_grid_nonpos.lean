-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb22_original_uniform_zero_contact_generator_signed_grid_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:25:51.958771+00:00
-- url     : https://prove2.me/submissions/f09c68b5-3757-4c66-8141-ff679212d650

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
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
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range (n + 1),
      if Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) = 0 then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.drift - q * w 0 +
            (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0  := by
  have hboundary :=
    avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
      X hX hBV hFinite q w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
  apply Finset.sum_nonpos
  intro i hi
  split_ifs with hz
  · have he : 0 ≤ Real.exp (-(q * (u n i : ℝ))) := (Real.exp_pos _).le
    have hwidth : (0 : ℝ) ≤ (u n (i + 1) : ℝ) - u n i := by
      exact sub_nonneg.mpr (by exact_mod_cast hmono n i (Finset.mem_range.mp hi))
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos he hboundary) hwidth
  · exact le_refl 0
