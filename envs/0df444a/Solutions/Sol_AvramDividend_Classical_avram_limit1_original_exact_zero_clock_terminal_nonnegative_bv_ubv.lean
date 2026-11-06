-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_original_exact_zero_clock_terminal_nonnegative_bv_ubv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:43:06.424353+00:00
-- url     : https://prove2.me/submissions/ef6e1346-503a-4da1-819a-1cef61056f5e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_book_reserve_terminal_nonnegative_separate_gradient

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Nonnegative original discounted terminal for the exact zero-clock branch
    and both BV and UBV regularity classes, without terminal vanishing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ ω, 0 ≤ Term ω := by
  intro ω
  rw [hTerm ω, hW ω]
  refine mul_nonneg (Real.exp_nonneg _) ?_
  split_ifs with hbefore
  · by_cases hBV : X.BoundedVariation
    · exact avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
        X w C hC hw0 hw_cont hw_neg (hw_smooth.2 hBV) hw_grad
        x hx hxc D hD ω (τ ω)
    · exact avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
        X w C hw0 hw_cont hw_neg (hw_smooth.1 hBV) hw_grad
        x hxc D hD ω (τ ω)
  · exact avram_wave5_03_actual_book_reserve_terminal_nonnegative_separate_gradient
      X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD ω (τ ω)
