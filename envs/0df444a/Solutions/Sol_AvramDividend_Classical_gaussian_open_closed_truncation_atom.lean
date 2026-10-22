-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_open_closed_truncation_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:27:37.952364+00:00
-- url     : https://prove2.me/submissions/89c9ebd3-efc8-4331-893f-76daefcb8890

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


/-- The jump truncation at one differs between a strict cutoff
and an inclusive cutoff by exactly the unit boundary atom. -/
theorem solution (z : ℝ) :
    (if z < 1 then z else 0) =
      (if z ≤ 1 then z else 0) -
        (if z = 1 then (1 : ℝ) else 0) := by
  rcases lt_trichotomy z 1 with hlt | heq | hgt
  · have hle : z ≤ 1 := le_of_lt hlt
    have hne : z ≠ 1 := ne_of_lt hlt
    simp [hlt, hle, hne]
  · subst z
    simp
  · have hnlt : ¬ z < 1 := not_lt_of_gt hgt
    have hnle : ¬ z ≤ 1 := not_le.mpr hgt
    have hne : z ≠ 1 := ne_of_gt hgt
    simp [hnlt, hnle, hne]
