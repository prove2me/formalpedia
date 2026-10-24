-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_scale_right_ratio_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:03:38.74298+00:00
-- url     : https://prove2.me/submissions/864ef1fd-22d3-4354-9d5d-c4cf349ac106

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Substitution of a one-step upward scale ratio into an immediate geometric reward. -/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (ε A B : ℝ) (hA : A ≠ 0) (hAB : A - B ≠ 0) :
    ε / (1 - B / A) = ε * A / (A - B) := by
  have hden : 1 - B / A = (A - B) / A := by
    field_simp
    <;> ring
  rw [hden]
  field_simp [hA, hAB]
  <;> ring
