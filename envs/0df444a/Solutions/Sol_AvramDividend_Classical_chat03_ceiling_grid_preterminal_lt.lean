-- Prove2me | solution 1 for AvramDividend.Classical.chat03_ceiling_grid_preterminal_lt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T05:24:33.682212+00:00
-- url     : https://prove2.me/submissions/170298b4-0f80-4cd9-adb5-6a7b8e09550c

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-!
Every uniform-grid point strictly before the ceiling index of T/h
lies strictly before the physical horizon T, for any positive mesh h.
This permits clipping only the final grid sample without changing
any earlier first-passage observation.
-/
theorem solution (T h : ℝ≥0) (hh : 0 < h) (j : ℕ)
    (hj : j < Nat.ceil (T / h)) :
    (j : ℝ≥0) * h < T := by
  have hjdiv : (j : ℝ≥0) < T / h := Nat.lt_ceil.mp hj
  calc
    (j : ℝ≥0) * h < (T / h) * h :=
      mul_lt_mul_of_pos_right hjdiv hh
    _ = T := div_mul_cancel₀ T (ne_of_gt hh)
