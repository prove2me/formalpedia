-- Prove2me | solution 1 for AvramDividend.Classical.poisson_predictable_finite_rank_compensation_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:52:02.456491+00:00
-- url     : https://prove2.me/submissions/21aa1070-372c-4968-bc34-878037949b52

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

/-- Finite-rank predictable marked-Poisson compensation.
The individual products are integrable; there is no compensator or Dynkin
identity among the assumptions. -/
theorem solution
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (s : Finset ι)
    (H : ι → Ω → ℝ) (f : ι → E → ℝ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hHm : ∀ i ∈ s, Measurable (H i))
    (hHi : ∀ i ∈ s, Integrable (H i) μ)
    (hf : ∀ i ∈ s, Measurable (f i))
    (hfI : ∀ i ∈ s, Integrable (f i) ν)
    (hPast : ∀ i ∈ s, IndepFun (H i)
      (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (hProdInt : ∀ i ∈ s,
      Integrable (fun ω =>
        H i ω * ∑ n ∈ Finset.range (K ω), f i (Y n ω)) μ) :
    (∫ ω, ∑ i ∈ s,
      H i ω * (∑ n ∈ Finset.range (K ω), f i (Y n ω)) ∂μ) =
      ∑ i ∈ s, (∫ ω, H i ω ∂μ) *
        ((r : ℝ) * ∫ y, f i y ∂ν) := by
  rw [integral_finset_sum s hProdInt]
  apply Finset.sum_congr rfl
  intro i hi
  exact poisson_predictable_marked_compensation_closed_ws01b
    μ ν (H i) (hHm i hi) (hHi i hi)
    K Y hKm r hKlaw hYm hYL hCountMarks (hPast i hi)
    (f i) (hf i hi) (hfI i hi)
