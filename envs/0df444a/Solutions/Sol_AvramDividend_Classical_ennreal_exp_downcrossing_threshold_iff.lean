-- Prove2me | solution 1 for AvramDividend.Classical.ennreal_exp_downcrossing_threshold_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:57:20.498311+00:00
-- url     : https://prove2.me/submissions/8fe15fb5-b255-4668-9e59-f775393c6d7b

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

theorem solution
    (ε b y : ℝ) (hε : 0 < ε) :
    (ENNReal.ofReal (Real.exp (ε * b)) ≤
      ENNReal.ofReal (Real.exp (-ε * y))) ↔ y ≤ -b := by
  rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _),
    Real.exp_le_exp]
  constructor
  · intro h
    have hmul : ε * b ≤ ε * (-y) := by
      simpa only [mul_neg, neg_mul] using h
    have hb : b ≤ -y := le_of_mul_le_mul_left hmul hε
    linarith
  · intro h
    have hb : b ≤ -y := by linarith
    have hmul : ε * b ≤ ε * (-y) :=
      mul_le_mul_of_nonneg_left hb (le_of_lt hε)
    simpa only [mul_neg, neg_mul] using hmul
