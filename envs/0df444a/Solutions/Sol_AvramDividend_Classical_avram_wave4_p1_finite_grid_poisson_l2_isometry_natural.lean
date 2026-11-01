-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_finite_grid_poisson_l2_isometry_natural
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:34:10.545213+00:00
-- url     : https://prove2.me/submissions/b7b6c86a-7bf3-4b95-80ea-d9a60bc84c31

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_grid_predictable_poisson_l2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_grid_poisson_prefix_memLp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat BigOperators

/-- Practical finite-grid predictable Poisson-count L² isometry with only
natural square-integrable predictable weights and joint past independence.
Individual and prefix L² assumptions are proved, not imposed. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → ℝ) (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (hHm : ∀ i, Measurable (H i))
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hKInt : ∀ i, Integrable (fun ω => (K i ω : ℝ) - (r i : ℝ)) P)
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
  have hHlp : ∀ i, MemLp (H i) 2 P := by
    intro i
    exact (memLp_two_iff_integrable_sq (hHm i).aestronglyMeasurable).2 (hHSq i)
  have hIndep : ∀ i, IndepFun (H i) (K i) P := by
    intro i
    simpa [Function.comp_def] using
      (hJointPast i).comp
        (by fun_prop : Measurable (fun p : ℝ × ℝ => p.2))
        (by fun_prop : Measurable (fun n : ℕ => n))
  have hPrefix :=
    AvramDividend.Classical.avram_wave4_p1_finite_grid_poisson_prefix_memLp
      P H K r hHm hHSq hKm hKlaw hIndep
  exact AvramDividend.Classical.avram_wave4_p1_finite_grid_predictable_poisson_l2_isometry
    P H K r hHm hHlp hHSq hKm hKlaw hKInt hPrefix hJointPast n
