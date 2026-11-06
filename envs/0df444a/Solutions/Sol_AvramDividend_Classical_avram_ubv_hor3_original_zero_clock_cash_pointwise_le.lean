-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_zero_clock_cash_pointwise_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:22:29.965604+00:00
-- url     : https://prove2.me/submissions/bb3a0e44-92db-45b9-8079-69e5acdf789d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_discounted_terminal_nonnegative_of_cap_payoff_sign
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
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
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (ω : Ω) (hZero : τ ω = 0) :
    Cash ω ≤ w x := by
  have hCapSign : ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → 0 ≤ w y :=
    avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
      w C hw0 hw_cont hw_smooth hw_grad
  have hTermNonneg : 0 ≤ Term ω := by
    rw [hTerm ω]
    exact avram_p4_e_localise_original_discounted_terminal_nonnegative_of_cap_payoff_sign
      X x C D hD hxc q τ W hW w hw_neg hCapSign ω
  have hPath :=
    avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
      X x q w C D hD hjump τ W Cash Term hW hCash hTerm ω hZero
  linarith
