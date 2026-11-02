-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_piecewise_terminal_nonnegative_bv_ubv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:28:01.597985+00:00
-- url     : https://prove2.me/submissions/8627abb6-fe03-4dcc-813c-2cc3ac53d7be

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
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
noncomputable section

/-- Terminal source sign at any bounded or unbounded clock, by actual BV/UBV
smoothness branches and the chronological postpayment/ruin terminal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ᵐ ω ∂P, 0 ≤ Term ω := by
  have hWnonneg : ∀ ω, 0 ≤ w (W ω) := by
    intro ω
    rw [hW ω]
    by_cases hruin : (τ ω : ℝ≥0∞) < ruinTime X x D ω
    · rw [if_pos hruin]
      by_cases hBV : X.BoundedVariation
      · exact avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
          X w C hC hw0 hw_cont hw_neg (hw_smooth.2 hBV) hw_grad
          x hx hxc D hD ω (τ ω)
      · exact avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
          X w C hw0 hw_cont hw_neg (hw_smooth.1 hBV) hw_grad
          x hxc D hD ω (τ ω)
    · rw [if_neg hruin]
      exact avram_wave5_03_actual_book_reserve_terminal_nonnegative_separate_gradient
        X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hxc D hD ω (τ ω)
  filter_upwards [] with ω
  rw [hTerm ω]
  exact mul_nonneg (Real.exp_pos _).le (hWnonneg ω)
