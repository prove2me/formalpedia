-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_strict_open_discounted_cash_pathwise_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:46:46.196386+00:00
-- url     : https://prove2.me/submissions/88b28bda-f9c0-458a-9808-12e7817d9323

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine original strictly open pre-rightpayment discounted payout is
finite at every deterministic finite horizon, including singular cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (b : ℝ≥0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by
  have hFin := avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
    D hD.1.1 ω (ruinTime X x D ω) b q hq
  have hIncl : paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ) ⊆
      paymentTimes (ruinTime X x D ω) ∩ Iic (b : ℝ) := by
    intro t ht
    exact ⟨ht.1, le_of_lt ht.2.2⟩
  exact lt_of_le_of_lt (lintegral_mono_set hIncl) hFin
