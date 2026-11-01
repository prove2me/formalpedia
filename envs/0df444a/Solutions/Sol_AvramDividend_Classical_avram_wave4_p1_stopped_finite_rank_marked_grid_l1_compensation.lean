-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_stopped_finite_rank_marked_grid_l1_compensation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:31:02.524997+00:00
-- url     : https://prove2.me/submissions/2119cfec-5115-489b-a785-7ad6729d0bb3

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_rank_marked_cell_l1_compensation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators

/-- Genuinely time-predictable finite-grid Campbell identity for a stopped
original-space marked Poisson kernel of arbitrary finite mark rank. -/
theorem solution
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E)
    (s : Finset ι) (m : ℕ)
    (H : ℕ → ι → Ω → ℝ) (τ : Ω → ℕ) (f : ℕ → ι → E → ℝ)
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E) (r : ℕ → ℝ≥0)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) μ)
    (hYm : ∀ i n, Measurable (Y i n))
    (hYL : ∀ i n, HasLaw (Y i n) ν μ)
    (hCountMarks : ∀ i,
      IndepFun (K i) (fun ω (n : ℕ) => Y i n ω) μ)
    (hWm : ∀ i a, a ∈ s →
      Measurable (fun ω => if i < τ ω then H i a ω else 0))
    (hWi : ∀ i a, a ∈ s →
      Integrable (fun ω => if i < τ ω then H i a ω else 0) μ)
    (hPast : ∀ i a, a ∈ s →
      IndepFun (fun ω => if i < τ ω then H i a ω else 0)
        (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (hfm : ∀ i a, a ∈ s → Measurable (f i a))
    (hfI : ∀ i a, a ∈ s → Integrable (f i a) ν) :
    Integrable (fun ω => ∑ i ∈ Finset.range m, ∑ a ∈ s,
      (if i < τ ω then H i a ω else 0) *
        ((∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
          (r i : ℝ) * ∫ z, f i a z ∂ν)) μ ∧
    (∫ ω, ∑ i ∈ Finset.range m, ∑ a ∈ s,
      (if i < τ ω then H i a ω else 0) *
        ((∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
          (r i : ℝ) * ∫ z, f i a z ∂ν) ∂μ) = 0 := by
  classical
  have hCell (i : ℕ) :
      Integrable (fun ω => ∑ a ∈ s,
        (if i < τ ω then H i a ω else 0) *
          ((∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
            (r i : ℝ) * ∫ z, f i a z ∂ν)) μ ∧
      (∫ ω, ∑ a ∈ s,
        (if i < τ ω then H i a ω else 0) *
          ((∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
            (r i : ℝ) * ∫ z, f i a z ∂ν) ∂μ) = 0 := by
    exact avram_wave4_p1_finite_rank_marked_cell_l1_compensation
      μ ν s (fun a ω => if i < τ ω then H i a ω else 0)
      (f i) (K i) (Y i) (hKm i) (r i) (hKlaw i)
      (hYm i) (hYL i) (hCountMarks i)
      (hWm i) (hWi i) (hPast i) (hfm i) (hfI i)
  constructor
  · exact integrable_finset_sum (Finset.range m)
      (fun i hi => (hCell i).1)
  · rw [integral_finset_sum (Finset.range m)
      (fun i hi => (hCell i).1)]
    exact Finset.sum_eq_zero (fun i hi => (hCell i).2)
