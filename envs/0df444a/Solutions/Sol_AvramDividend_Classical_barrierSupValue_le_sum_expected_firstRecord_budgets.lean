-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_le_sum_expected_firstRecord_budgets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:03:15.781993+00:00
-- url     : https://prove2.me/submissions/461e3091-ffbd-41ba-9fe4-a6550ace9dcd

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_full_reward_indicator_expectation
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! Tonelli converts countable first-record upper budgets into a dividend value bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P,
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω))
      ≤ (∑' n, w n ω)) :
    barrierSupValue X a q ≤ (∑' n, ∫⁻ ω, w n ω ∂P) := by
  rw [barrierSupValue_eq_full_reward_indicator_expectation X a q]
  calc
    (∫⁻ ω, ∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω) ∂P) ≤
      (∫⁻ ω, ∑' n, w n ω ∂P) := lintegral_mono_ae hbudget
    _ = (∑' n, ∫⁻ ω, w n ω ∂P) := lintegral_tsum hw
