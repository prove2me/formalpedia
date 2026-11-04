-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_p4f_real_cash_exact_lintegral_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:22:50.979874+00:00
-- url     : https://prove2.me/submissions/f28ba5b6-0a94-41d6-ab11-c11f9680114e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true P4-F real stopped Cash faithfully represents its finite original ENNReal integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) :
    0 ≤ Cash ω ∧
    ENNReal.ofReal (Cash ω) =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by
  have hfin :=
    avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
      D hD ω (ruinTime X x D ω) (τ ω) q hq
  rw [hCash ω]
  exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ne_top_of_lt hfin)⟩
