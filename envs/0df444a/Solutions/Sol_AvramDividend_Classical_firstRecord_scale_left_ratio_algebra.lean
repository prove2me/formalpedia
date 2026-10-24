-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_scale_left_ratio_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:03:42.823896+00:00
-- url     : https://prove2.me/submissions/373b9cca-eb20-4d98-bfb4-98d0aa8605f5

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Substitution of a one-step downward scale ratio into a delayed geometric reward. -/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (ε A B : ℝ) (hA : A ≠ 0) (hAB : A - B ≠ 0) :
    ε * (B / A) / (1 - B / A) = ε * B / (A - B) := by
  have hden : 1 - B / A = (A - B) / A := by
    field_simp
    <;> ring
  rw [hden]
  field_simp [hA, hAB]
  <;> ring
