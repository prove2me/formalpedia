-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a266_full_physical_source_positive_small_large_raw_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:57:29.076236+00:00
-- url     : https://prove2.me/submissions/9c06bfb9-1bff-4d44-b873-0c2901b6fadb

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
noncomputable section

theorem solution
    {Ω : Type*} (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (r e : ℕ → Ω → ℝ) (δ : ℝ) (ω : Ω) :
    max (∑ i ∈ S, if A i ω then e i ω else 0) 0 ≤
      max (∑ i ∈ S, if A i ω ∧ |r i ω| < δ
        then e i ω else 0) 0 +
      max (∑ i ∈ S, if A i ω ∧ δ ≤ |r i ω|
        then e i ω else 0) 0 := by
  have hsplit (i : ℕ) :
      (if A i ω then e i ω else 0) =
        (if A i ω ∧ |r i ω| < δ then e i ω else 0) +
        (if A i ω ∧ δ ≤ |r i ω| then e i ω else 0) := by
    by_cases ha : A i ω
    · by_cases hr : |r i ω| < δ
      · simp [ha, hr, not_le.mpr hr]
      · simp [ha, hr, le_of_not_gt hr]
    · simp [ha]
  have hsum :
      (∑ i ∈ S, if A i ω then e i ω else 0) =
      (∑ i ∈ S, if A i ω ∧ |r i ω| < δ then e i ω else 0) +
      (∑ i ∈ S, if A i ω ∧ δ ≤ |r i ω| then e i ω else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hsplit i)
  rw [hsum]
  refine max_le ?_ ?_
  · exact add_le_add (le_max_left _ _) (le_max_left _ _)
  · have h1 := le_max_right
      (∑ i ∈ S, if A i ω ∧ |r i ω| < δ then e i ω else 0) 0
    have h2 := le_max_right
      (∑ i ∈ S, if A i ω ∧ δ ≤ |r i ω| then e i ω else 0) 0
    linarith
