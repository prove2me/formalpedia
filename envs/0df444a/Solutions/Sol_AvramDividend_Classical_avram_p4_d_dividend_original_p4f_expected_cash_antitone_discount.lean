-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_p4f_expected_cash_antitone_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:47:22.915532+00:00
-- url     : https://prove2.me/submissions/0935dda8-d129-49bf-9d1e-99774845582f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_cash_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Expected literal source stopped dividend cash decreases as the discount rate increases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (Cash₁ Cash₂ : Ω → ℝ)
    (hCash₁ : ∀ ω, Cash₁ ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q₁ * s))) ∂(dividendMeasure D ω)).toReal)
    (hCash₂ : ∀ ω, Cash₂ ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q₂ * s))) ∂(dividendMeasure D ω)).toReal)
    (hI₁ : Integrable Cash₁ P) (hI₂ : Integrable Cash₂ P) :
    (∫ ω, Cash₂ ω ∂P) ≤ (∫ ω, Cash₁ ω ∂P) := by
  apply integral_mono hI₂ hI₁
  intro ω
  have hmono := avram_p4_d_dividend_original_true_stopped_cash_antitone_discount
    D ω (ruinTime X x D ω) (τ ω) q₁ q₂ hq
  have hfin :=
    avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
      D hD ω (ruinTime X x D ω) (τ ω) q₁ hq₁
  rw [hCash₁ ω, hCash₂ ω]
  exact ENNReal.toReal_mono (ne_top_of_lt hfin) hmono
