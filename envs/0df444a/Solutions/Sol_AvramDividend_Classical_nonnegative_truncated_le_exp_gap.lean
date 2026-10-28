-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_truncated_le_exp_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:55:18.728549+00:00
-- url     : https://prove2.me/submissions/b583f5e0-814c-4170-81a6-e7c7135e1dd6

import Theorems.Thm_AvramDividend_Classical_exp_gap_dominates_half_interval
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A capped nonnegative increment is bounded by a fixed multiple of its exponential deficit. -/
theorem solution
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    x ≤ 4 * a * (1 - Real.exp (-(x / (2 * a)))) := by
  have ha2 : 0 < 2 * a := by positivity
  have hu0 : 0 ≤ x / (2 * a) :=
    div_nonneg hx0 ha2.le
  have huHalf : x / (2 * a) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ ha2).mpr
    nlinarith
  have hExp :=
    AvramDividend.Classical.exp_gap_dominates_half_interval
      (x / (2 * a)) hu0 huHalf
  have hScale :=
    mul_le_mul_of_nonneg_left hExp ha2.le
  have hCancel : (2 * a) * (x / (2 * a)) = x := by
    field_simp [ne_of_gt ha]
  calc
    x = (2 * a) * (x / (2 * a)) := hCancel.symm
    _ ≤ (2 * a) * (2 * (1 - Real.exp (-(x / (2 * a))))) := hScale
    _ = 4 * a * (1 - Real.exp (-(x / (2 * a)))) := by ring
