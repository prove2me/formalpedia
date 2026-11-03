-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_finite_horizon_value_budget_from_stopped_and_terminal_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:15:00.683448+00:00
-- url     : https://prove2.me/submissions/a48ab3b9-c38b-4d94-a5f6-4ecf4209eac5

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_horizon_reward_le_min_clock_plus_terminal_atom
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Explicit expected true source payout budget from two genuine
    original-measure budgets, keeping any terminal dividend atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (hT : 0 ≤ T) (B A : ℝ≥0∞)
    (hStopped :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B)
    (hTerminal :
      (∫⁻ ω, ∫⁻ t in
        (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ A) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B + A := by
  exact le_trans
    (avram_wave7_11_original_expected_horizon_reward_le_min_clock_plus_terminal_atom
      X x D hD q T hT)
    (add_le_add hStopped hTerminal)
