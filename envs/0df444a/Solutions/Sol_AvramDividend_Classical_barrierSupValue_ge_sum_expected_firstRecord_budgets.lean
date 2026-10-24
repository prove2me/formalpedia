-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_ge_sum_expected_firstRecord_budgets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:03:09.951732+00:00
-- url     : https://prove2.me/submissions/7bf7d96b-982c-4e40-aa5a-26ed33e71c9a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_full_reward_indicator_expectation
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! Tonelli converts a pathwise countable first-record budget into a value lower bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P, (∑' n, w n ω) ≤
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω))) :
    (∑' n, ∫⁻ ω, w n ω ∂P) ≤ barrierSupValue X a q := by
  rw [barrierSupValue_eq_full_reward_indicator_expectation X a q]
  calc
    (∑' n, ∫⁻ ω, w n ω ∂P) =
      (∫⁻ ω, ∑' n, w n ω ∂P) := by
        exact (lintegral_tsum hw).symm
    _ ≤ _ := lintegral_mono_ae hbudget
