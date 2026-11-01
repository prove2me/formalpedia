-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_stopped_predictable_marked_finite_grid_l2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:25:22.009143+00:00
-- url     : https://prove2.me/submissions/ade14fc9-e833-439b-854e-f4b0c4167577

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_two_cell_marked_l2_increment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_marked_finite_prefix_memLp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators

/-- Exact L² isometry of an original-path stopped finite-grid predictable
marked-Poisson compensated integral, with independent future increments. -/
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
          (r i : ℝ) * ∫ z, f i z ∂ν)))
    (hPrefixMeas : ∀ i, Measurable (fun ω =>
      ∑ j ∈ Finset.range i,
        (if j < τ ω then H j ω else 0) *
          ((∑ n ∈ Finset.range (K j ω), f j (Y j n ω)) -
            (r j : ℝ) * ∫ z, f j z ∂ν)))
    (hJointPast : ∀ i, IndepFun (fun ω =>
      ((∑ j ∈ Finset.range i,
        (if j < τ ω then H j ω else 0) *
          ((∑ n ∈ Finset.range (K j ω), f j (Y j n ω)) -
            (r j : ℝ) * ∫ z, f j z ∂ν)),
       if i < τ ω then H i ω else 0))
      (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (m : ℕ) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range m,
        (if i < τ ω then H i ω else 0) *
          ((∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) -
            (r i : ℝ) * ∫ z, f i z ∂ν)) ^ 2) μ ∧
    (∫ ω, (∑ i ∈ Finset.range m,
      (if i < τ ω then H i ω else 0) *
        ((∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) -
          (r i : ℝ) * ∫ z, f i z ∂ν)) ^ 2 ∂μ) =
      ∑ i ∈ Finset.range m,
        (∫ ω, (if i < τ ω then H i ω else 0) ^ 2 ∂μ) *
          ((r i : ℝ) * ∫ z, f i z ^ 2 ∂ν) := by
  classical
  let W : ℕ → Ω → ℝ := fun i ω => if i < τ ω then H i ω else 0
  let Z : ℕ → Ω → ℝ := fun i ω =>
    W i ω * ((∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) -
      (r i : ℝ) * ∫ z, f i z ∂ν)
  have hPrefixLp : ∀ i, MemLp
      (fun ω => ∑ j ∈ Finset.range i, Z j ω) 2 μ := by
    exact avram_wave4_p1_stopped_marked_finite_prefix_memLp
      μ ν H τ K Y r f hKm hKlaw hYm hYL hYi hCountMarks
      hWm hW2 hPast hf hfI hf2 hIncMeas
  change Integrable (fun ω => (∑ i ∈ Finset.range m, Z i ω) ^ 2) μ ∧
    (∫ ω, (∑ i ∈ Finset.range m, Z i ω) ^ 2 ∂μ) =
      ∑ i ∈ Finset.range m, (∫ ω, W i ω ^ 2 ∂μ) *
        ((r i : ℝ) * ∫ z, f i z ^ 2 ∂ν)
  induction m with
  | zero =>
      constructor
      · simpa using
          (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) μ)
      · simp
  | succ m ih =>
      have hWlp : MemLp (W m) 2 μ :=
        (memLp_two_iff_integrable_sq (hWm m).aestronglyMeasurable).2 (hW2 m)
      have hPrevSq : Integrable
          (fun ω => (∑ i ∈ Finset.range m, Z i ω) ^ 2) μ :=
        (memLp_two_iff_integrable_sq
          (hPrefixMeas m).aestronglyMeasurable).1 (hPrefixLp m)
      have hStep := avram_wave4_p1_two_cell_marked_l2_increment
        μ ν
        (fun ω => ∑ i ∈ Finset.range m, Z i ω) (W m)
        (hPrefixMeas m) (hWm m)
        (hPrefixLp m) hPrevSq hWlp (hW2 m)
        (K m) (Y m) (hKm m) (r m) (hKlaw m)
        (hYm m) (hYL m) (hYi m)
        (hCountMarks m) (hJointPast m)
        (f m) (hf m) (hfI m) (hf2 m)
      have hPoint :
          (fun ω => (∑ i ∈ Finset.range (m + 1), Z i ω) ^ 2) =
          (fun ω => ((∑ i ∈ Finset.range m, Z i ω) + Z m ω) ^ 2) := by
        funext ω
        simp only [Finset.sum_range_succ]
      constructor
      · rw [hPoint]
        exact hStep.1
      · calc
          (∫ ω, (∑ i ∈ Finset.range (m + 1), Z i ω) ^ 2 ∂μ) =
            (∫ ω, ((∑ i ∈ Finset.range m, Z i ω) + Z m ω) ^ 2 ∂μ) := by
              rw [hPoint]
          _ = (∫ ω, (∑ i ∈ Finset.range m, Z i ω) ^ 2 ∂μ) +
              (∫ ω, W m ω ^ 2 ∂μ) *
                ((r m : ℝ) * ∫ z, f m z ^ 2 ∂ν) := hStep.2
          _ = ∑ i ∈ Finset.range (m + 1),
                (∫ ω, W i ω ^ 2 ∂μ) *
                  ((r i : ℝ) * ∫ z, f i z ^ 2 ∂ν) := by
                rw [Finset.sum_range_succ, ih.2]
