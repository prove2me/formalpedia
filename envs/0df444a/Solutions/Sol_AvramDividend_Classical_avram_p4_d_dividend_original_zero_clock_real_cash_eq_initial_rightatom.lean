-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:03:10.32453+00:00
-- url     : https://prove2.me/submissions/c48f63d4-8a57-42a2-813c-c85fbc369abd

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
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
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) (hZero : τ ω = 0) :
    Cash ω =
      (ENNReal.ofReal (rightLimit D 0 ω - D 0 ω)).toReal := by
  have hCash0 : Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
    simpa [hZero] using hCash ω
  calc
    Cash ω =
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal := hCash0
    _ = ((dividendMeasure D ω) ({0} : Set ℝ)).toReal :=
      congrArg ENNReal.toReal
        (avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
          D ω (ruinTime X x D ω) q)
    _ = (ENNReal.ofReal (rightLimit D 0 ω - D 0 ω)).toReal :=
      congrArg ENNReal.toReal
        (dividendMeasure_singleton_eq_rightLimit_sub D hD ω 0)
