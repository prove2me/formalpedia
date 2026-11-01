-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_finite_rank_marked_poisson_cell_l2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:21:38.37135+00:00
-- url     : https://prove2.me/submissions/a29d0a3b-502a-4104-8511-4004a82f3b36

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_two_past_weights_marked_cell_covariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators

/-- On the genuine original marked Poisson cell, a finite sum of predictable
past×mark tensors has L² energy equal to its actual finite Gram quadratic form. -/
theorem solution
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (s : Finset ι) (H : ι → Ω → ℝ) (f : ι → E → ℝ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0)
    (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hYi : iIndepFun Y μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hHm : ∀ i ∈ s, Measurable (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun ω => H i ω ^ 2) μ)
    (hPast : ∀ i ∈ s,
      IndepFun (H i) (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (hPastSum : ∀ i ∈ s, ∀ j ∈ s,
      IndepFun (fun ω => H i ω + H j ω)
        (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (hfm : ∀ i ∈ s, Measurable (f i))
    (hfI : ∀ i ∈ s, Integrable (f i) ν)
    (hf2 : ∀ i ∈ s, MemLp (f i) 2 ν) :
    let A : ι → Ω → ℝ := fun i ω =>
      H i ω * ((∑ n ∈ Finset.range (K ω), f i (Y n ω)) -
        (r : ℝ) * ∫ z, f i z ∂ν)
    Integrable (fun ω => (∑ i ∈ s, A i ω) ^ 2) μ ∧
      (∫ ω, (∑ i ∈ s, A i ω) ^ 2 ∂μ) =
        ∑ i ∈ s, ∑ j ∈ s,
          (∫ ω, H i ω * H j ω ∂μ) * (r : ℝ) *
            (∫ z, f i z * f j z ∂ν) := by
  classical
  let A : ι → Ω → ℝ := fun i ω =>
    H i ω * ((∑ n ∈ Finset.range (K ω), f i (Y n ω)) -
      (r : ℝ) * ∫ z, f i z ∂ν)
  change Integrable (fun ω => (∑ i ∈ s, A i ω) ^ 2) μ ∧
    (∫ ω, (∑ i ∈ s, A i ω) ^ 2 ∂μ) =
      ∑ i ∈ s, ∑ j ∈ s,
        (∫ ω, H i ω * H j ω ∂μ) * (r : ℝ) *
          (∫ z, f i z * f j z ∂ν)
  have hCross (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      Integrable (fun ω => A i ω * A j ω) μ ∧
        (∫ ω, A i ω * A j ω ∂μ) =
          (∫ ω, H i ω * H j ω ∂μ) * (r : ℝ) *
            (∫ z, f i z * f j z ∂ν) := by
    exact avram_wave4_p1_two_past_weights_marked_cell_covariance
      μ ν (H i) (H j) (hHm i hi) (hHm j hj)
      (hH2 i hi) (hH2 j hj) K Y hKm r hKlaw
      hYm hYL hYi hCountMarks
      (hPast i hi) (hPast j hj) (hPastSum i hi j hj)
      (f i) (f j) (hfm i hi) (hfm j hj)
      (hfI i hi) (hfI j hj) (hf2 i hi) (hf2 j hj)
  have hInnerInt (i : ι) (hi : i ∈ s) :
      Integrable (fun ω => ∑ j ∈ s, A i ω * A j ω) μ :=
    integrable_finset_sum s (fun j hj => (hCross i hi j hj).1)
  have hDoubleInt :
      Integrable (fun ω => ∑ i ∈ s, ∑ j ∈ s,
        A i ω * A j ω) μ :=
    integrable_finset_sum s (fun i hi => hInnerInt i hi)
  have hSquarePoint (ω : Ω) :
      (∑ i ∈ s, A i ω) ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, A i ω * A j ω := by
    calc
      _ = (∑ i ∈ s, A i ω) * (∑ j ∈ s, A j ω) := by ring
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
  have hSquareFun :
      (fun ω => (∑ i ∈ s, A i ω) ^ 2) =
        (fun ω => ∑ i ∈ s, ∑ j ∈ s, A i ω * A j ω) := by
    funext ω
    exact hSquarePoint ω
  constructor
  · rw [hSquareFun]
    exact hDoubleInt
  · rw [hSquareFun, integral_finset_sum s (fun i hi => hInnerInt i hi)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finset_sum s (fun j hj => (hCross i hi j hj).1)]
    apply Finset.sum_congr rfl
    intro j hj
    exact (hCross i hi j hj).2
