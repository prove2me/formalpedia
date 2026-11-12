-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b21_original_physical_grid_compensator_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:43:42.494227+00:00
-- url     : https://prove2.me/submissions/5aae6862-a887-493e-8aac-dcf324f8b1c4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original finite-grid negative-jump compensator is nonpositive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (n : ℕ) (ω : Ω) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        (∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Z i + z) - w (Z i)) ∂X.ν) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0 := by
  dsimp only
  apply Finset.sum_nonpos
  intro i hi
  split_ifs with h
  · have hsign := avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
        C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
        X.ν (Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i))
        (le_of_lt h.2.1) (le_of_lt h.2.2)
    have hinner :
        (∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
              (u n i) + z) -
            w (Function.leftLim
              (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
                (u n i))) ∂X.ν) ≤ 0 := by
      rw [integral_const_mul]
      exact mul_nonpos_of_nonneg_of_nonpos
        (Real.exp_pos _).le hsign
    have hwidth :
        0 ≤ ((u n (i + 1) : ℝ) - (u n i : ℝ)) := by
      exact sub_nonneg.mpr (by
        exact_mod_cast hmono n i (Finset.mem_range.mp hi))
    exact mul_nonpos_of_nonpos_of_nonneg hinner hwidth
  · exact le_refl 0
