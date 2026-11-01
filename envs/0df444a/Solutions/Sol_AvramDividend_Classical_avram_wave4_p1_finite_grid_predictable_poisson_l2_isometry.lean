-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_finite_grid_predictable_poisson_l2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:23:50.093744+00:00
-- url     : https://prove2.me/submissions/1a4cc6bb-dba7-404e-b5e6-3106d179cbfc

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_two_cell_predictable_poisson_l2_increment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat BigOperators

/-- A genuinely original-path predictable finite-grid Poisson-count L²
isometry, under explicit joint-past independence at each cell. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → ℝ) (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (hHm : ∀ i, Measurable (H i))
    (hHlp : ∀ i, MemLp (H i) 2 P)
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hKInt : ∀ i, Integrable (fun ω => (K i ω : ℝ) - (r i : ℝ)) P)
    (hPrefixLp : ∀ i, MemLp (fun ω =>
      ∑ j ∈ Finset.range i, H j ω * ((K j ω : ℝ) - (r j : ℝ))) 2 P)
    (hJointPast : ∀ i, IndepFun (fun ω =>
      ((∑ j ∈ Finset.range i, H j ω * ((K j ω : ℝ) - (r j : ℝ))), H i ω))
      (K i) P)
    (n : ℕ) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range n, H i ω * ((K i ω : ℝ) - (r i : ℝ))) ^ 2) P ∧
      (∫ ω, (∑ i ∈ Finset.range n,
        H i ω * ((K i ω : ℝ) - (r i : ℝ))) ^ 2 ∂P) =
          ∑ i ∈ Finset.range n,
            (r i : ℝ) * ∫ ω, (H i ω) ^ 2 ∂P := by
  classical
  induction n with
  | zero =>
      constructor
      · simpa using
          (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) P)
      · simp
  | succ n ih =>
      have hStep :=
        AvramDividend.Classical.avram_wave4_p1_two_cell_predictable_poisson_l2_increment
          P
          (fun ω =>
            ∑ j ∈ Finset.range n, H j ω * ((K j ω : ℝ) - (r j : ℝ)))
          (H n)
          (hPrefixLp n) ih.1
          (hHm n) (hHlp n) (hHSq n)
          (K n) (hKm n) (r n) (hKlaw n)
          (hKInt n) (hJointPast n)
      have hPoint :
          (fun ω =>
            (∑ i ∈ Finset.range (n + 1),
              H i ω * ((K i ω : ℝ) - (r i : ℝ))) ^ 2) =
          (fun ω =>
            ((∑ i ∈ Finset.range n,
              H i ω * ((K i ω : ℝ) - (r i : ℝ))) +
              H n ω * ((K n ω : ℝ) - (r n : ℝ))) ^ 2) := by
        funext ω
        simp only [Finset.sum_range_succ]
      constructor
      · rw [hPoint]
        exact hStep.1
      · calc
          (∫ ω, (∑ i ∈ Finset.range (n + 1),
            H i ω * ((K i ω : ℝ) - (r i : ℝ))) ^ 2 ∂P) =
            (∫ ω, ((∑ i ∈ Finset.range n,
              H i ω * ((K i ω : ℝ) - (r i : ℝ))) +
              H n ω * ((K n ω : ℝ) - (r n : ℝ))) ^ 2 ∂P) := by
                rw [hPoint]
          _ = (∫ ω, (∑ i ∈ Finset.range n,
              H i ω * ((K i ω : ℝ) - (r i : ℝ))) ^ 2 ∂P) +
              (r n : ℝ) * ∫ ω, (H n ω) ^ 2 ∂P := hStep.2
          _ = ∑ i ∈ Finset.range (n + 1),
                (r i : ℝ) * ∫ ω, (H i ω) ^ 2 ∂P := by
                rw [Finset.sum_range_succ, ih.2]
