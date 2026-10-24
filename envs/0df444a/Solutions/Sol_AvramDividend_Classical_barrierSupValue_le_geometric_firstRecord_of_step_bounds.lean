-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_le_geometric_firstRecord_of_step_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:09:20.557344+00:00
-- url     : https://prove2.me/submissions/bc0be2dc-1bda-4763-bac7-47bd7fc6a212

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_sum_expected_firstRecord_budgets
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! Geometric upper first-record estimates imply a bound for the stopped barrier value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q ε p : ℝ)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P, (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      (∑' n, w n ω))
    (hstep : ∀ n, (∫⁻ ω, w n ω ∂P) ≤
      ENNReal.ofReal (ε * p ^ (n + 1))) :
    barrierSupValue X a q ≤ (∑' n, ENNReal.ofReal (ε * p ^ (n + 1))) := by
  exact (barrierSupValue_le_sum_expected_firstRecord_budgets X a q w hw hbudget).trans
    (ENNReal.tsum_le_tsum hstep)
