-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_all_random_stop_paid_cash_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:30:25.266059+00:00
-- url     : https://prove2.me/submissions/a415574b-8a17-4763-a6ae-c888918961b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_survival_discounted_full_cash_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_complete_paid_cash_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτle : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by
  exact avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
    D hD ω (ruinTime X x D ω) (τ ω) q hq
