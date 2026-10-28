-- Prove2me | solution 1 for AvramDividend.Classical.bv_renewal_tail_lower_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:15:24.167791+00:00
-- url     : https://prove2.me/submissions/39b7ee62-aa8f-4193-9143-6e8acea93fce

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (d q w tail slope R : ℝ)
    (hd : 0 < d) (hq : 0 ≤ q) (hw : 0 ≤ w) (hR : 0 ≤ R)
    (hEq : d * slope = q * w + tail * (1 / d) + R) :
    tail / d ^ 2 ≤ slope := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hd2 : 0 < d ^ 2 := pow_pos hd 2
  have hnon : 0 ≤ d * (q * w + R) :=
    mul_nonneg (le_of_lt hd) (add_nonneg (mul_nonneg hq hw) hR)
  have heq : d ^ 2 * slope = d * (q * w + R) + tail := by
    calc
      d ^ 2 * slope = d * (d * slope) := by ring
      _ = d * (q * w + tail * (1 / d) + R) := by rw [hEq]
      _ = d * (q * w + R) + tail := by
        field_simp [hd0]
        ring
  apply (div_le_iff₀ hd2).2
  calc
    tail ≤ d ^ 2 * slope := by rw [heq]; linarith
    _ = slope * d ^ 2 := by ring
