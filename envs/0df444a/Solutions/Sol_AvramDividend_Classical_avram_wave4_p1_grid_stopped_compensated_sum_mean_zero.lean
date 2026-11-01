-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_grid_stopped_compensated_sum_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:40:53.376069+00:00
-- url     : https://prove2.me/submissions/03bd1df8-dcd2-4fd2-9780-bb9de3e760db

import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_product_integrable_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

/-- A finite grid of stopped predictable marked Poisson increments has zero
centred expectation. Product L1 integrability is proved from cellwise
past/future independence instead of assumed. -/
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
    (hfI : ∀ i ∈ s, Integrable (f i) ν) :
    (∫ ω, ∑ i ∈ s,
      ((if i < τ ω then H i ω else 0) *
          (∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) -
        (if i < τ ω then H i ω else 0) *
          ((r i : ℝ) * ∫ y, f i y ∂ν)) ∂μ) = 0 := by
  have hProdInt : ∀ i ∈ s,
      Integrable (fun ω =>
        (if i < τ ω then H i ω else 0) *
          ∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) μ := by
    intro i hi
    exact poisson_predictable_marked_product_integrable_ws01b
      μ ν (fun ω => if i < τ ω then H i ω else 0)
      (hWm i hi) (hWi i hi) (K i) (Y i)
      (hKm i hi) (r i) (hKlaw i hi)
      (hYm i hi) (hYL i hi) (hCountMarks i hi) (hPast i hi)
      (f i) (hf i hi) (hfI i hi)
  have hCompInt : ∀ i ∈ s,
      Integrable (fun ω =>
        (if i < τ ω then H i ω else 0) *
          ((r i : ℝ) * ∫ y, f i y ∂ν)) μ := by
    intro i hi
    exact (hWi i hi).mul_const _
  have hGrid :=
    integral_finset_sum s (fun i hi => (hProdInt i hi).sub (hCompInt i hi))
  simp only [Pi.sub_apply] at hGrid
  rw [hGrid]
  apply Finset.sum_eq_zero
  intro i hi
  have hCellSub := integral_sub (hProdInt i hi) (hCompInt i hi)
  rw [hCellSub]
  rw [poisson_predictable_marked_compensation_closed_ws01b
    μ ν (fun ω => if i < τ ω then H i ω else 0)
    (hWm i hi) (hWi i hi) (K i) (Y i)
    (hKm i hi) (r i) (hKlaw i hi)
    (hYm i hi) (hYL i hi) (hCountMarks i hi) (hPast i hi)
    (f i) (hf i hi) (hfI i hi)]
  rw [integral_mul_const]
  ring
