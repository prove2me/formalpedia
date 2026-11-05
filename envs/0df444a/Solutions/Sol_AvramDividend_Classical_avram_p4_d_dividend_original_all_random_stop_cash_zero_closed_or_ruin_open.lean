-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_all_random_stop_cash_zero_closed_or_ruin_open
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:51:37.221711+00:00
-- url     : https://prove2.me/submissions/4d8556aa-bd59-4db1-949e-f2ba9915743f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_random_stop_closed_or_ruin_open_cash
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-! The original stopping cash identity splits the zero-clock initial atom
and the exact positive-clock ruin-excluded payment interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hτle : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (ω : Ω) :
    Cash ω =
      if τ ω = 0 then
        (ENNReal.ofReal (rightLimit D 0 ω - D 0 ω)).toReal
      else if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        (∫⁻ s in Icc (0 : ℝ) (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal
      else
        (∫⁻ s in Ico (0 : ℝ) (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal := by
  by_cases hz : τ ω = 0
  · simpa [hz] using
      (avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
        X x q D hD τ Cash hCash ω hz)
  · have h0 : (0 : ℝ≥0) ≤ τ ω := zero_le
    have hp : 0 < τ ω := lt_of_le_of_ne h0 (Ne.symm hz)
    simpa [hz] using
      (avram_p4_d_dividend_original_positive_random_stop_closed_or_ruin_open_cash
        X x q D τ Cash hCash hτle ω hp)
