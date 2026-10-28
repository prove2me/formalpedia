-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_ge_left_scale_quotient_of_actual_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:30:51.54652+00:00
-- url     : https://prove2.me/submissions/4637a455-d604-458a-bbd7-15bb4b0efa16

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat08_record_grid_stopped_weights_aemeasurable
import Theorems.Thm_AvramDividend_Classical_stopped_firstRecord_grid_pathwise_budget
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_left_scale_quotient_of_record_budgets
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical

/-- The verified pathwise dividend budget turns actual killed-grid estimates into the left scale quotient. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (a q ε : ℝ)
    (hq : 0 ≤ q) (hε : 0 < ε)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a)
    (hgrid : ∀ n : ℕ,
      ENNReal.ofReal (ε * (W (a - ε) / W a) ^ (n + 1)) ≤
        (∫⁻ ω,
      if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) :
    ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
      barrierSupValue X a q := by
  let w : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
    else 0
  have hw (n : ℕ) : AEMeasurable (w n) P := by
    simpa only [w, zero_add] using
      (chat08_record_grid_stopped_weights_aemeasurable
        X a 0 q ε (fun k => k + 1) n)
  have hbudget : ∀ᵐ ω ∂P, (∑' n, w n ω) ≤
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    simpa only [w, zero_add] using
      (stopped_firstRecord_grid_pathwise_budget
        X ω a q 0 ε hq (le_refl 0) hε)
  have hstep (n : ℕ) :
      ENNReal.ofReal (ε * (W (a - ε) / W a) ^ (n + 1)) ≤
        (∫⁻ ω, w n ω ∂P) := by
    simpa only [w] using hgrid n
  exact barrierSupValue_ge_left_scale_quotient_of_record_budgets
    X W a q ε (le_of_lt hε) hWa hWleft hWinc w hw hbudget hstep
