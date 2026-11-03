-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_original_admissible_zero_start_zero_horizon_cash_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:58:20.886415+00:00
-- url     : https://prove2.me/submissions/f577f1c7-7fd1-4de0-ba32-8e3ba91b69d5

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_at_zero_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_any_cap_original_zero_start_right_dividend_vanishes
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Complete original Stieltjes cash at T=0 vanishes for an admissible
zero-start control, independently of the reserve cap and of ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 C D)
    (q : ℝ) (σ : ℝ≥0∞) (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 := by
  rw [truncated_dividend_payoff_at_zero_eq_initial_atom D hD.1.1 q σ ω,
    avram_wave6_08_any_cap_original_zero_start_right_dividend_vanishes X C D hD ω,
    hD.1.1.1 ω]
  simp
