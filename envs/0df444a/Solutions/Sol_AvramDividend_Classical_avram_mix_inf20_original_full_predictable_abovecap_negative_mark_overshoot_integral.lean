-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_full_predictable_abovecap_negative_mark_overshoot_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:16:25.040409+00:00
-- url     : https://prove2.me/submissions/0a955827-d717-4b94-9354-d810d56cfdd7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (μ : Measure ((ℝ≥0 × Ω) × ℝ)) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if C.toReal < Y p.1 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (V (Y p.1 + p.2) - V (Y p.1) - deriv V (Y p.1) * p.2)
      else 0
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if C.toReal < Y p.1 then
        Real.exp (-(q * (p.1.1 : ℝ))) * max 0 (-(Y p.1 + p.2))
      else 0
    Integrable H μ → Integrable G μ →
      (∫ p, H p ∂μ) ≤ (∫ p, G p ∂μ) := by
  dsimp only
  intro hHI hGI
  apply integral_mono hHI hGI
  intro p
  dsimp only
  by_cases hy : C.toReal <
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2) p.1.1
  · simp only [if_pos hy]
    exact mul_le_mul_of_nonneg_left
      (avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
        C hC hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad
        _ p.2 hy)
      (le_of_lt (Real.exp_pos _))
  · simp only [if_neg hy, le_refl]
