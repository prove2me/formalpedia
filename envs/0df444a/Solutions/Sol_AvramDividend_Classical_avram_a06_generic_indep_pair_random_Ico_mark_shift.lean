-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_generic_indep_pair_random_Ico_mark_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:46:59.341346+00:00
-- url     : https://prove2.me/submissions/c3626b46-5fbf-4a76-8209-3a5190b69f5d

import Mathlib.Probability.IdentDistrib
import Theorems.Thm_AvramDividend_Classical_avram_a06_generic_indep_count_dependent_mark_shift_joint_law
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- A random-interval sum is a shifted fixed-prefix sum, and the joint
    count-conditioned shift law transfers its distribution. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → Fin 2 → ℕ) (M : Ω → ℕ → ℝ)
    (hN : AEMeasurable N P)
    (hM : AEMeasurable M P)
    (hNM : IndepFun N M P)
    (hshift : ∀ m : ℕ,
      IdentDistrib (fun ω j => M ω (m + j)) M P P) :
    IdentDistrib
      (fun ω => ∑ j ∈ Finset.Ico (N ω 0) (N ω 1), M ω j)
      (fun ω => ∑ j ∈ Finset.range (N ω 1 - N ω 0), M ω j) P P := by
  let F : (Fin 2 → ℕ) × (ℕ → ℝ) → ℝ :=
    fun p => ∑ j ∈ Finset.range (p.1 1 - p.1 0), p.2 j
  have hF : Measurable F := by
    refine measurable_from_prod_countable_right ?_
    intro n
    exact Finset.measurable_sum (Finset.range (n 1 - n 0))
      (fun j hj => measurable_pi_apply j)
  have hJoint :=
    AvramDividend.Classical.avram_a06_generic_indep_count_dependent_mark_shift_joint_law
      P N M hN hM hNM hshift
  have hDistr := hJoint.comp hF
  convert hDistr using 1
  · funext ω
    simp only [Function.comp_apply, F]
    rw [Finset.sum_Ico_eq_sum_range]
  · rfl
