-- Prove2me | solution 1 for AvramDividend.Classical.drawdown_strict_exit_strip_of_sup_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T05:46:13.595138+00:00
-- url     : https://prove2.me/submissions/6e53552b-b9c3-4237-9023-9c6dfb0a5fcd

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (a h S X : ℝ) (hS0 : 0 ≤ S) (hSh : S ≤ h) :
    (X < -a → a < S - X) ∧
    (a < S - X → X < h - a) ∧
    (h - a ≤ X → S - X ≤ a) ∧
    (S - X ≤ a → -a ≤ X) := by
  constructor
  · intro hX
    linarith
  constructor
  · intro hDrawdown
    linarith
  constructor
  · intro hAbove
    linarith
  · intro hSurvive
    linarith
