-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB94_monotone_step_indicator_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:58:25.716758+00:00
-- url     : https://prove2.me/submissions/4a07a3a7-cbff-416d-9ebd-bec326eac4eb

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped BigOperators
noncomputable section

/-- Consecutive half-open interval indicators telescope on a monotone grid. -/
theorem solution (f : ℕ → ℝ) (hf : Monotone f)
    (t : ℝ) (N : ℕ) :
    (Finset.range N).sum (fun j =>
      if f j ≤ t ∧ t < f (j + 1) then (1 : ℝ) else 0) =
    (if f 0 ≤ t then (1 : ℝ) else 0) -
      (if f N ≤ t then (1 : ℝ) else 0) := by
  have hcell (j : ℕ) :
      (if f j ≤ t ∧ t < f (j + 1) then (1 : ℝ) else 0) =
      (if f j ≤ t then (1 : ℝ) else 0) -
        (if f (j + 1) ≤ t then (1 : ℝ) else 0) := by
    by_cases h₁ : f j ≤ t
    · by_cases h₂ : t < f (j + 1)
      · simp [h₁, h₂, not_le.mpr h₂]
      · have h₂' : f (j + 1) ≤ t := le_of_not_gt h₂
        simp [h₁, h₂, h₂']
    · have h₂ : ¬ f (j + 1) ≤ t :=
        fun h => h₁ ((hf (Nat.le_succ j)).trans h)
      simp [h₁, h₂]
  simp_rw [hcell]
  simpa using
    (Finset.sum_range_sub'
      (fun j : ℕ => if f j ≤ t then (1 : ℝ) else 0) N)