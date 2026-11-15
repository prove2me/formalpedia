-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_actual_finite_mark_step_source_terminal_jump_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:54:08.065336+00:00
-- url     : https://prove2.me/submissions/bfc928a9-5ae0-4fb6-bca1-bd8a93ff58c8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (S : Finset ℝ≥0) (z : ℝ≥0 → ℝ) (t : ℝ≥0) :
    (∑ u ∈ S, if u ≤ t then z u else 0) -
      (∑ u ∈ S, if u < t then z u else 0) =
        if t ∈ S then z t else 0 := by
  classical
  have hOne (u : ℝ≥0) :
      (if u ≤ t then z u else 0) - (if u < t then z u else 0) =
      if u = t then z u else 0 := by
    rcases lt_trichotomy u t with h | h | h
    · have hu : u ≠ t := ne_of_lt h
      simp [le_of_lt h, h, hu]
    · subst u
      simp
    · have hu : ¬ u ≤ t := not_le.mpr h
      have ht : ¬ u < t := not_lt.mpr (le_of_lt h)
      have hne : u ≠ t := ne_of_gt h
      simp [hu, ht, hne]
  calc
    (∑ u ∈ S, if u ≤ t then z u else 0) -
      (∑ u ∈ S, if u < t then z u else 0) =
        ∑ u ∈ S,
          ((if u ≤ t then z u else 0) - (if u < t then z u else 0)) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ u ∈ S, if u = t then z u else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hOne u
    _ = if t ∈ S then z t else 0 := by simp
