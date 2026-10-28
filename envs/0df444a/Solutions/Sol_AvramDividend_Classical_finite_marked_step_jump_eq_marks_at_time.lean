-- Prove2me | solution 1 for AvramDividend.Classical.finite_marked_step_jump_eq_marks_at_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:09:40.159636+00:00
-- url     : https://prove2.me/submissions/30144343-ded0-41e0-bf4b-c38bc6f5ce59

import Mathlib

open scoped NNReal BigOperators
theorem solution
    {ι : Type*} (S : Finset ι) (τ : ι → ℝ≥0) (w : ι → ℝ) (t : ℝ≥0) :
    (∑ i ∈ S, if τ i ≤ t then w i else 0) -
      (∑ i ∈ S, if τ i < t then w i else 0) =
    ∑ i ∈ S, if τ i = t then w i else 0 := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases lt_trichotomy (τ i) t with h | h | h
  · simp [h.le, h, h.ne]
  · simp [h]
  · simp [not_le.mpr h, not_lt.mpr h.le, h.ne']
