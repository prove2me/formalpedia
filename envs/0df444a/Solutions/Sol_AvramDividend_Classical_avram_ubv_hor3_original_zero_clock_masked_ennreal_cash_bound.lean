-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_zero_clock_masked_ennreal_cash_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:11:37.037199+00:00
-- url     : https://prove2.me/submissions/fdb813b9-6e54-4a00-91e0-c8376d1b7657

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_exact_zero_or_preruin_terminal_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    (∫⁻ ω, if τ ω = 0 then ENNReal.ofReal (Cash ω) else 0 ∂P) ≤
      (∫⁻ ω, if τ ω = 0 then ENNReal.ofReal (w x) else 0 ∂P) := by
  have hTermAE : ∀ᵐ ω ∂P, 0 ≤ Term ω :=
    avram_wave7_08_source_exact_zero_or_preruin_terminal_nonnegative
      X hBV q w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hx hxc D hD τ W Term hW hTerm
  apply lintegral_mono_ae
  filter_upwards [hTermAE] with ω hTermPos
  by_cases hZero : τ ω = 0
  · simp only [if_pos hZero]
    apply ENNReal.ofReal_le_ofReal
    have hPath :=
      avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
        X x q w C D hD hjump τ W Cash Term hW hCash hTerm ω hZero
    linarith
  · simp [hZero]
