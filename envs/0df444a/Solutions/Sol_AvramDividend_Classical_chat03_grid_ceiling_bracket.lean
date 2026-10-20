-- Prove2me | solution 1 for AvramDividend.Classical.chat03_grid_ceiling_bracket
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:41:36.014981+00:00
-- url     : https://prove2.me/submissions/020e28bf-f8a2-4d72-b635-2f505f71d670

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp

/-!
Every positive grid spacing h has a first grid point at or after time t,
strictly less than h later. This is the deterministic mesh lemma needed
for dyadic detection of open strict passage.
-/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (t h : ℝ) (ht : 0 ≤ t) (hh : 0 < h) :
    t ≤ (Nat.ceil (t / h) : ℝ) * h ∧
      (Nat.ceil (t / h) : ℝ) * h < t + h := by
  have hq : 0 ≤ t / h := div_nonneg ht hh.le
  have hbelow : t / h ≤ (Nat.ceil (t / h) : ℝ) :=
    Nat.le_ceil (t / h)
  have habove : (Nat.ceil (t / h) : ℝ) < t / h + 1 :=
    Nat.ceil_lt_add_one hq
  have hmul : (t / h) * h = t := by
    field_simp
  constructor
  · calc
      t = (t / h) * h := hmul.symm
      _ ≤ (Nat.ceil (t / h) : ℝ) * h :=
        mul_le_mul_of_nonneg_right hbelow hh.le
  · calc
      (Nat.ceil (t / h) : ℝ) * h < (t / h + 1) * h :=
        mul_lt_mul_of_pos_right habove hh
      _ = t + h := by rw [add_mul, hmul, one_mul]
