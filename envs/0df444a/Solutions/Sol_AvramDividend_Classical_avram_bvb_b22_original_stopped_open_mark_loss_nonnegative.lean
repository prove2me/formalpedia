-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b22_original_stopped_open_mark_loss_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:11:20.22852+00:00
-- url     : https://prove2.me/submissions/e92a0363-f205-4607-a0af-fc6b0b271b34

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original stopped open-cap discounted negative-mark loss is pointwise nonnegative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    0 ≤ if (t : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < U t ∧ ENNReal.ofReal (U t) < C then
          -(Real.exp (-(q * (t : ℝ))) *
            ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν)
        else 0 := by
  dsimp only
  split_ifs with h
  · have hsign := avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
      C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
      X.ν (Function.leftLim
        (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) t)
      (le_of_lt h.2.1) (le_of_lt h.2.2)
    exact neg_nonneg.mpr
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hsign)
  · exact le_refl 0
