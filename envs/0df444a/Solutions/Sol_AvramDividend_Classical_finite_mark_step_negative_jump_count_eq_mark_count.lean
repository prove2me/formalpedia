-- Prove2me | solution 1 for AvramDividend.Classical.finite_mark_step_negative_jump_count_eq_mark_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:01:16.830153+00:00
-- url     : https://prove2.me/submissions/0e7ef5bb-0016-43e0-9ea0-a2fd2937e058

import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_finite_marked_step_jump_eq_single_of_injective

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal BigOperators

theorem solution
    {ι : Type*} (S : Finset ι) (τ : ι → ℝ≥0) (w : ι → ℝ)
    (hτ : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j → i = j)
    (a : ℝ) :
    (∑ t ∈ S.image τ,
      if (∑ j ∈ S, if τ j ≤ t then w j else 0) -
         (∑ j ∈ S, if τ j < t then w j else 0) < -a
      then (1 : ℕ) else 0) =
    ∑ i ∈ S, if w i < -a then (1 : ℕ) else 0 := by
  classical
  have hinj : Set.InjOn τ (S : Set ι) := by
    intro i hi j hj heq
    exact hτ i hi j hj heq
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [finite_marked_step_jump_eq_single_of_injective S τ w hτ i hi]