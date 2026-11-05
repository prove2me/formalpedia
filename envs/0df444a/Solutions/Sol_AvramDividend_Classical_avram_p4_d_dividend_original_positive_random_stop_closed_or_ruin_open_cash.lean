-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_positive_random_stop_closed_or_ruin_open_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:51:38.60972+00:00
-- url     : https://prove2.me/submissions/fa5bb578-81ae-49d6-bcfe-51e3249e7960

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_paymentTimes_strict_horizon_eq_Icc
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_ruin_cash_excludes_terminal_atom
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
    (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hτle : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (ω : Ω) (hPos : 0 < τ ω) :
    Cash ω =
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        (∫⁻ s in Icc (0 : ℝ) (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal
      else
        (∫⁻ s in Ico (0 : ℝ) (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal := by
  by_cases hstrict : (τ ω : ℝ≥0∞) < ruinTime X x D ω
  · simp only [if_pos hstrict]
    rw [hCash ω,
      avram_wave8_21_original_paymentTimes_strict_horizon_eq_Icc
        (ruinTime X x D ω) (τ ω) hstrict]
  · simp only [if_neg hstrict]
    have hRuin : ruinTime X x D ω = (τ ω : ℝ≥0∞) :=
      le_antisymm (le_of_not_gt hstrict) (hτle ω)
    exact avram_p4_d_dividend_original_positive_ruin_cash_excludes_terminal_atom
      X x D q τ Cash hCash ω hPos hRuin
