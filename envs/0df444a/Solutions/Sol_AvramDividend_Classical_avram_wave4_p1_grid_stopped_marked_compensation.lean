-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_grid_stopped_marked_compensation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:20:11.087984+00:00
-- url     : https://prove2.me/submissions/385810d2-88bd-45ce-8a08-d53e7826dfcf

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

/-- Compensation for a finite deterministic time grid stopped at a random grid
index. Each stopped cell coefficient is past-independent of that cell's future
Poisson count and mark family. The identity is derived from the genuine Poisson
law and conditional independence, without assuming compensation. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (s : Finset ℕ)
    (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (r : ℕ → ℝ≥0) (f : ℕ → E → ℝ)
    (hKm : ∀ i ∈ s, Measurable (K i))
    (hKlaw : ∀ i ∈ s, HasLaw (K i) (poissonMeasure (r i)) μ)
    (hYm : ∀ i ∈ s, ∀ n, Measurable (Y i n))
    (hYL : ∀ i ∈ s, ∀ n, HasLaw (Y i n) ν μ)
    (hCountMarks : ∀ i ∈ s,
      IndepFun (K i) (fun ω (n : ℕ) => Y i n ω) μ)
    (hWm : ∀ i ∈ s,
      Measurable (fun ω => if i < τ ω then H i ω else 0))
    (hWi : ∀ i ∈ s,
      Integrable (fun ω => if i < τ ω then H i ω else 0) μ)
    (hPast : ∀ i ∈ s,
      IndepFun (fun ω => if i < τ ω then H i ω else 0)
        (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (hf : ∀ i ∈ s, Measurable (f i))
    (hfI : ∀ i ∈ s, Integrable (f i) ν)
    (hProdInt : ∀ i ∈ s,
      Integrable (fun ω =>
        (if i < τ ω then H i ω else 0) *
          ∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) μ) :
    (∫ ω, ∑ i ∈ s,
      (if i < τ ω then H i ω else 0) *
        (∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) ∂μ) =
      ∑ i ∈ s, (∫ ω, (if i < τ ω then H i ω else 0) ∂μ) *
        ((r i : ℝ) * ∫ y, f i y ∂ν) := by
  rw [integral_finset_sum s hProdInt]
  apply Finset.sum_congr rfl
  intro i hi
  exact poisson_predictable_marked_compensation_closed_ws01b
    μ ν (fun ω => if i < τ ω then H i ω else 0)
    (hWm i hi) (hWi i hi) (K i) (Y i)
    (hKm i hi) (r i) (hKlaw i hi)
    (hYm i hi) (hYL i hi) (hCountMarks i hi) (hPast i hi)
    (f i) (hf i hi) (hfI i hi)
