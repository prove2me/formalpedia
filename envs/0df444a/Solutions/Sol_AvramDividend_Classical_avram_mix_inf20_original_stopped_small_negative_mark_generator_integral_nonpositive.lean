-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_stopped_small_negative_mark_generator_integral_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:38:35.311775+00:00
-- url     : https://prove2.me/submissions/d6483db3-d4b6-441e-89d5-f4bedeaa6f8b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_bounded_nearzero_true_generator_mark_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) (hδcap : δ ≤ C.toReal)
    (μ : Measure ((ℝ≥0 × Ω) × ℝ)) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if C.toReal < Y p.1 ∧ -δ < p.2 ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          SpectrallyNegativeLevy.generatorIntegrand V (Y p.1) p.2
      else 0
    Integrable H μ → (∫ p, H p ∂μ) ≤ 0 := by
  dsimp only
  intro hI
  apply integral_nonpos_of_ae
  filter_upwards [] with p
  by_cases hmask : C.toReal <
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2) p.1.1 ∧
      -δ < p.2 ∧ p.2 < 0
  · simp only [if_pos hmask]
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos _))
      (avram_mix_inf20_original_finitecap_bounded_nearzero_true_generator_mark_nonpos
        C hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad
        δ _ p.2 hδ hδone hδcap hmask.1 hmask.2.2 hmask.2.1)
  · simp [if_neg hmask]
