-- Prove2me | solution 1 for AvramDividend.Classical.poisson_predictable_marked_product_integrable_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:05:51.968249+00:00
-- url     : https://prove2.me/submissions/a897691d-26ee-4243-aa76-501ff9efcfc6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_random_mark_sum_integrable_ws01b
import Theorems.Thm_AvramDividend_Classical_variable_finite_marks_sum_measurable_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat


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
    Integrable (fun ω =>
      H ω * ∑ n ∈ Finset.range (K ω), f (Y n ω)) μ := by
  have hS := poisson_random_mark_sum_integrable_ws01b μ ν K Y hKm r hKlaw hYm hYL hCountMarks f hf hfI
  have hg := variable_finite_marks_sum_measurable_ws01b f hf
  have hind : IndepFun H (fun ω => ∑ n ∈ Finset.range (K ω), f (Y n ω)) μ :=
    hPast.comp measurable_id hg
  exact hind.integrable_mul hHi hS
