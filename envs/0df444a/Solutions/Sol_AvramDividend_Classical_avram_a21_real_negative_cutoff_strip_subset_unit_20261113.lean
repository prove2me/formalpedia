-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_real_negative_cutoff_strip_subset_unit_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:24:45.794033+00:00
-- url     : https://prove2.me/submissions/2470e8fe-b0d6-4bb0-a0d5-6c0dfe3619c5

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- Every negative cutoff strip used for the original physical marked
Lévy process lies inside the unit-negative interval. -/
theorem solution
    (n m : ℕ) :
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))) ⊆
      Icc (-1 : ℝ) 0 := by
  intro z hz
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hm : 0 < (m : ℝ) + 1 := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnfrac : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ hn).mpr
    linarith
  have hmfrac : 0 < 1 / ((m : ℝ) + 1) := by positivity
  constructor
  · have hz0 : -(1 / ((n : ℝ) + 1)) < z := hz.1
    linarith
  · have hz1 : z ≤ -(1 / ((m : ℝ) + 1)) := hz.2
    linarith
