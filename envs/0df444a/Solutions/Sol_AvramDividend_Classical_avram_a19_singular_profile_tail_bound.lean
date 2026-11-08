-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_singular_profile_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:38:06.330531+00:00
-- url     : https://prove2.me/submissions/a8057fd2-e070-4455-93ed-9c0c19658919

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- The negative singular HJB profile dominates reciprocal surplus. -/
theorem solution (t : Real) (ht : 0 < t) (htsmall : t <= 1 / 4) :
    1 / t <= -(3 + t ^ 2 - 4 * t - 2 / t) := by
  have hprod : t * (1 / t) = 1 := by
    field_simp [ne_of_gt ht]
  have hrec : 4 <= 1 / t := by
    by_contra h
    have hlt : 1 / t < 4 := lt_of_not_ge h
    have hp : 0 < (4 - 1 / t) * t :=
      mul_pos (by linarith) ht
    nlinarith
  have hquadr : t ^ 2 <= 4 * t := by
    have hnonneg : 0 <= 4 - t := by linarith
    have hp := mul_nonneg (le_of_lt ht) hnonneg
    nlinarith
  have hupper : 3 + t ^ 2 - 4 * t <= 1 / t := by linarith
  have htwo : (2 : Real) / t = (1 / t) + (1 / t) := by ring
  rw [htwo]
  linarith [hupper]
