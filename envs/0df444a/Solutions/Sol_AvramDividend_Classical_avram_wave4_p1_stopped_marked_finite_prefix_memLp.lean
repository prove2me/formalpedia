-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_stopped_marked_finite_prefix_memLp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:15:53.407792+00:00
-- url     : https://prove2.me/submissions/30db0336-241e-45ae-b822-73af545f81c0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators

/-- Every finite prefix of stopped predictable marked-Poisson compensated
increments is L², without assuming any cross-cell orthogonality. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (r : ℕ → ℝ≥0) (f : ℕ → E → ℝ)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) μ)
    (hYm : ∀ i n, Measurable (Y i n))
    (hYL : ∀ i n, HasLaw (Y i n) ν μ)
    (hYi : ∀ i, iIndepFun (Y i) μ)
    (hCountMarks : ∀ i,
      IndepFun (K i) (fun ω (n : ℕ) => Y i n ω) μ)
    (hWm : ∀ i, Measurable
      (fun ω => if i < τ ω then H i ω else 0))
    (hW2 : ∀ i, Integrable
      (fun ω => (if i < τ ω then H i ω else 0) ^ 2) μ)
    (hPast : ∀ i,
      IndepFun (fun ω => if i < τ ω then H i ω else 0)
        (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (hf : ∀ i, Measurable (f i))
    (hfI : ∀ i, Integrable (f i) ν)
    (hf2 : ∀ i, MemLp (f i) 2 ν)
    (hIncMeas : ∀ i, Measurable (fun ω =>
      (if i < τ ω then H i ω else 0) *
        ((∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) -
          (r i : ℝ) * ∫ z, f i z ∂ν))) :
    ∀ m, MemLp (fun ω => ∑ i ∈ Finset.range m,
      (if i < τ ω then H i ω else 0) *
        ((∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) -
          (r i : ℝ) * ∫ z, f i z ∂ν)) 2 μ := by
  classical
  let Z : ℕ → Ω → ℝ := fun i ω =>
    (if i < τ ω then H i ω else 0) *
      ((∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) -
        (r i : ℝ) * ∫ z, f i z ∂ν)
  have hCell : ∀ i, MemLp (Z i) 2 μ := by
    intro i
    have hSquare := avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry
      μ ν (fun ω => if i < τ ω then H i ω else 0)
      (hWm i) (hW2 i)
      (K i) (Y i) (hKm i) (r i) (hKlaw i)
      (hYm i) (hYL i) (hYi i) (hCountMarks i) (hPast i)
      (f i) (hf i) (hfI i) (hf2 i)
    exact (memLp_two_iff_integrable_sq
      (hIncMeas i).aestronglyMeasurable).2 hSquare.1
  change ∀ m, MemLp (fun ω => ∑ i ∈ Finset.range m, Z i ω) 2 μ
  intro m
  induction m with
  | zero =>
      have hZeroMeas : AEStronglyMeasurable (fun _ : Ω => (0 : ℝ)) μ :=
        aestronglyMeasurable_const
      have hZero : MemLp (fun _ : Ω => (0 : ℝ)) 2 μ :=
        (memLp_two_iff_integrable_sq hZeroMeas).2 (by
          simpa using (integrable_const (0 : ℝ) :
            Integrable (fun _ : Ω => (0 : ℝ)) μ))
      simpa using hZero
  | succ m ih =>
      have hPoint :
          (fun ω => ∑ i ∈ Finset.range (m + 1), Z i ω) =
          (fun ω => ∑ i ∈ Finset.range m, Z i ω) + Z m := by
        funext ω
        simp only [Finset.sum_range_succ, Pi.add_apply]
      rw [hPoint]
      exact ih.add (hCell m)
