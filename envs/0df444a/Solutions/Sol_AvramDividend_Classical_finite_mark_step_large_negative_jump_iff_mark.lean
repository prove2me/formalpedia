-- Prove2me | solution 1 for AvramDividend.Classical.finite_mark_step_large_negative_jump_iff_mark
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:20:40.195022+00:00
-- url     : https://prove2.me/submissions/e0bee9d1-07d2-4120-a960-34b6b505bbd0

import Mathlib

open scoped NNReal BigOperators
theorem solution
    {ι : Type*} (S : Finset ι) (τ : ι → ℝ≥0) (w : ι → ℝ)
    (hτ : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j → i = j)
    (a : ℝ) (ha : 0 ≤ a) (t : ℝ≥0) :
    ((∑ j ∈ S, if τ j ≤ t then w j else 0) -
      (∑ j ∈ S, if τ j < t then w j else 0) < -a) ↔
      ∃ i ∈ S, τ i = t ∧ w i < -a := by
  classical
  have hdiff : (∑ j ∈ S, if τ j ≤ t then w j else 0) -
      (∑ j ∈ S, if τ j < t then w j else 0) = ∑ j ∈ S, if τ j = t then w j else 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy (τ j) t with h | h | h
    · simp [h.le, h, h.ne]
    · simp [h]
    · simp [not_le.2 h, not_lt.2 h.le, h.ne']
  rw [hdiff]
  by_cases hex : ∃ i ∈ S, τ i = t
  · obtain ⟨i, hi, hit⟩ := hex
    have : (∑ j ∈ S, if τ j = t then w j else 0) = w i := by
      rw [Finset.sum_eq_single i]
      · simp [hit]
      · intro j hj hji
        have : τ j ≠ t := fun h => hji (hτ j hj i hi (h.trans hit.symm))
        simp [this]
      · intro h; exact absurd hi h
    rw [this]
    constructor
    · intro h; exact ⟨i, hi, hit, h⟩
    · rintro ⟨k, hk, hkt, hw⟩
      rwa [hτ i hi k hk (hit.trans hkt.symm)]
  · have : (∑ j ∈ S, if τ j = t then w j else 0) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        have : τ j ≠ t := fun h => hex ⟨j, hj, h⟩
        simp [this]
    rw [this]
    constructor
    · intro h; linarith
    · rintro ⟨i, hi, hit, _⟩; exact absurd ⟨i, hi, hit⟩ hex
