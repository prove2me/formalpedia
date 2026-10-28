-- Prove2me | solution 1 for AvramDividend.Classical.finite_marked_step_jump_eq_single_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:54:49.28414+00:00
-- url     : https://prove2.me/submissions/6dd6a604-a30c-472b-81f1-b8329858a95e

import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open scoped NNReal BigOperators
theorem solution
    {ι : Type*} (S : Finset ι) (τ : ι → ℝ≥0) (w : ι → ℝ)
    (hτ : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j → i = j)
    (i : ι) (hi : i ∈ S) :
    (∑ j ∈ S, if τ j ≤ τ i then w j else 0) -
      (∑ j ∈ S, if τ j < τ i then w j else 0) = w i := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hne : τ j ≠ τ i := fun h => hji (hτ j hj i hi h)
    by_cases h : τ j < τ i
    · simp [h, h.le]
    · have : ¬ τ j ≤ τ i := fun h' => h (lt_of_le_of_ne h' hne)
      simp [h, this]
  · intro h; exact absurd hi h
