-- Prove2me | solution 1 for AvramDividend.Classical.poisson_predictable_marked_compensation_closed_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:32:43.544118+00:00
-- url     : https://prove2.me/submissions/50a5435a-4db0-4467-98ec-aad773a23499

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_simple_marked_compensation_ws01b
import Theorems.Thm_AvramDividend_Classical_variable_finite_marks_sum_measurable_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

/-- Predictable simple marked Poisson compensation without any extra
measurability or expectation hypothesis on the random-length mark sum. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E)
    (H : Ω → ℝ) (hHm : Measurable H) (hHi : Integrable H μ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hPast : IndepFun H
      (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable f ν) :
    (∫ ω, H ω * (∑ n ∈ Finset.range (K ω), f (Y n ω)) ∂μ) =
      (∫ ω, H ω ∂μ) * ((r : ℝ) * ∫ y, f y ∂ν) := by
  exact poisson_predictable_simple_marked_compensation_ws01b
    μ ν H hHm hHi K Y hKm r hKlaw hYm hYL
    hCountMarks hPast f hf hfI
    (variable_finite_marks_sum_measurable_ws01b f hf)
