-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_ge_of_ae_finite_firstRecord_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:36:21.89498+00:00
-- url     : https://prove2.me/submissions/3c47aa3c-636a-4358-9bfc-8366ea45505d

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_ae_finite_cell_budget_to_tsum
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_sum_expected_firstRecord_budgets
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical

/-! Finite record-cell bounds almost everywhere imply a bound on the expected stopped dividend reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (a q : ℝ)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hfinite : ∀ N : ℕ, ∀ᵐ ω ∂P,
      (∑ n ∈ Finset.range N, w n ω) ≤
        (∫⁻ t,
          if t ∈ paymentTimes (barrierRuinTime X a ω)
          then ENNReal.ofReal (Real.exp (-(q * t))) else 0
          ∂(dividendMeasure (runningSup X) ω))) :
    (∑' n, ∫⁻ ω, w n ω ∂P) ≤ barrierSupValue X a q := by
  apply barrierSupValue_ge_sum_expected_firstRecord_budgets X a q w hw
  exact firstRecord_ae_finite_cell_budget_to_tsum P w _ hfinite
