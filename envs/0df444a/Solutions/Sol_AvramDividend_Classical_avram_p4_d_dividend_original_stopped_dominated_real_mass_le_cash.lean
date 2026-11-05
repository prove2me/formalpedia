-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_stopped_dominated_real_mass_le_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:33:00.230893+00:00
-- url     : https://prove2.me/submissions/a7891ef7-8a7c-4c2c-a26b-3b3754708f38

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_dominated_mass_le_discounted_cash
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Actual finite-horizon discounted Cash dominates the ordinary real mass
of every Stieltjes submeasure, after the exact minimum discount factor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ν : Measure ℝ) (hdom : ν ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    ν.real (paymentTimes σ ∩ Iic (T : ℝ)) ≤
      (∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal /
          Real.exp (-(q * (T : ℝ))) := by
  have hCash :
      (∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤ :=
    avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
      D hD ω σ T q hq
  have hmass :=
    avram_p4_d_dividend_original_stopped_dominated_mass_le_discounted_cash
      D hD ω σ T ν hdom q hq
  have hreal := ENNReal.toReal_mono (ne_of_lt hCash) hmass
  rw [ENNReal.toReal_ofReal_mul _ _ (le_of_lt (Real.exp_pos _))] at hreal
  apply (le_div_iff₀ (Real.exp_pos _)).2
  simpa only [Measure.real, mul_comm] using hreal
