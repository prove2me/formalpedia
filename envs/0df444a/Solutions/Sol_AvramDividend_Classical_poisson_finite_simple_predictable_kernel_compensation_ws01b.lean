-- Prove2me | solution 1 for AvramDividend.Classical.poisson_finite_simple_predictable_kernel_compensation_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:19:35.379986+00:00
-- url     : https://prove2.me/submissions/c21cd57c-7bf8-4d43-9100-0a7797b9dc60

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

/-- Finite-rank predictable jump kernels: the marked compensation rule
holds for arbitrary finite sums of separable past-and-mark observables. -/
theorem solution
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (s : Finset ι) (H : ι → Ω → ℝ) (f : ι → E → ℝ)
    (hHm : ∀ i ∈ s, Measurable (H i))
    (hHi : ∀ i ∈ s, Integrable (H i) μ)
    (hFm : ∀ i ∈ s, Measurable (f i))
    (hFi : ∀ i ∈ s, Integrable (f i) ν)
    (hPast : ∀ i ∈ s, IndepFun (H i)
      (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (hTerms : ∀ i ∈ s,
      Integrable (fun ω => (H i ω) *
        (∑ n ∈ Finset.range (K ω), (f i) (Y n ω))) μ) :
    (∫ ω, ∑ i ∈ s, (H i ω) *
      (∑ n ∈ Finset.range (K ω), (f i) (Y n ω)) ∂μ) =
    ∑ i ∈ s, (∫ ω, H i ω ∂μ) *
      ((r : ℝ) * ∫ y, f i y ∂ν) := by
  rw [integral_finset_sum s hTerms]
  apply Finset.sum_congr rfl
  intro i hi
  exact poisson_predictable_marked_compensation_closed_ws01b
    μ ν (H i) (hHm i hi) (hHi i hi)
    K Y hKm r hKlaw hYm hYL hCountMarks
    (hPast i hi) (f i) (hFm i hi) (hFi i hi)
