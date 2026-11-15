-- Prove2me | solution 1 for AvramDividend.Classical.avram_a30_finite_marked_jump_accumulator_exact_left_jump_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:28:24.553017+00:00
-- url     : https://prove2.me/submissions/116c212c-a257-4935-a02a-82ad5e359dea

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal BigOperators
noncomputable section

/-- A finite causal marked-jump accumulator has jump equal to its mark at each supported time. -/
theorem solution (S : Finset ℝ≥0) (a : ℝ≥0 → ℝ) (t : ℝ≥0) :
    (∑ u ∈ S, if u ≤ t then a u else 0) -
      (∑ u ∈ S, if u < t then a u else 0) =
      if t ∈ S then a t else 0 := by
  classical
  have hTerm (u : ℝ≥0) :
      (if u ≤ t then a u else 0) -
        (if u < t then a u else 0) = if u = t then a u else 0 := by
    rcases lt_trichotomy u t with hlt | heq | hgt
    · simp [le_of_lt hlt, hlt, ne_of_lt hlt]
    · subst u
      simp
    · simp [not_le.mpr hgt, not_lt.mpr (le_of_lt hgt), ne_of_gt hgt]
  calc
    (∑ u ∈ S, if u ≤ t then a u else 0) -
        (∑ u ∈ S, if u < t then a u else 0) =
      ∑ u ∈ S, ((if u ≤ t then a u else 0) -
        (if u < t then a u else 0)) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ u ∈ S, if u = t then a u else 0 :=
      Finset.sum_congr rfl (fun u _ => hTerm u)
    _ = if t ∈ S then a t else 0 := by
      simp [Finset.sum_ite_eq]
