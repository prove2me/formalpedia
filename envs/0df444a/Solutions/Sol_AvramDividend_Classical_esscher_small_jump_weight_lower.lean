-- Prove2me | solution 1 for AvramDividend.Classical.esscher_small_jump_weight_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:39:17.697632+00:00
-- url     : https://prove2.me/submissions/c786ee67-ef6a-4e27-82b5-974bdf9265ad

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Uniformly positive lower weight on small negative jumps under Esscher tilt. -/
theorem solution (φ y : ℝ) (hφ : 0 ≤ φ) (hy : -1 ≤ y) :
    ENNReal.ofReal (Real.exp (-φ)) ≤
      ENNReal.ofReal (Real.exp (φ * y)) := by
  have hmul : φ * (-1) ≤ φ * y :=
    mul_le_mul_of_nonneg_left hy hφ
  have hlin : -φ ≤ φ * y := by
    nlinarith
  exact ENNReal.ofReal_le_ofReal ((Real.exp_le_exp).2 hlin)
