-- Prove2me | solution 1 for AvramDividend.Classical.chat03_nnreal_grid_ceiling_bracket
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:56:24.823679+00:00
-- url     : https://prove2.me/submissions/103026fe-1446-44f6-a103-8cd4087044fd

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

/-! Concrete first grid sample after an NNReal time, with exact one-step bound. -/
theorem solution
    (t h : ℝ≥0) (hh : 0 < h) :
    t ≤ (Nat.ceil (t / h) : ℝ≥0) * h ∧
      (Nat.ceil (t / h) : ℝ≥0) * h < t + h := by
  have hq : 0 ≤ t / h := zero_le
  have hbelow : t / h ≤ (Nat.ceil (t / h) : ℝ≥0) :=
    Nat.le_ceil (t / h)
  have habove : (Nat.ceil (t / h) : ℝ≥0) < t / h + 1 :=
    Nat.ceil_lt_add_one hq
  have hmul : (t / h) * h = t := by
    field_simp
  constructor
  · calc
      t = (t / h) * h := hmul.symm
      _ ≤ (Nat.ceil (t / h) : ℝ≥0) * h :=
        mul_le_mul_of_nonneg_right hbelow (show 0 ≤ h from zero_le)
  · calc
      (Nat.ceil (t / h) : ℝ≥0) * h < (t / h + 1) * h :=
        mul_lt_mul_of_pos_right habove hh
      _ = t + h := by rw [add_mul, hmul, one_mul]
