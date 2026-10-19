-- Prove2me | solution 2 for CohnElkies.saddleSmallRadiusVariable_halfIntegerFactor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:21:30.028585+00:00
-- url     : https://prove2.me/submissions/9e98f3ee-ce0d-4883-9e5d-076044ba10fc

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    (ε : ℝ) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    r ^ (2 * N + 1) *
      Real.exp
        (((2 * N + 1 : ℕ) : ℝ) *
          (Real.log Real.pi / 2 +
            saddleShellDerivativeOne ε)) =
      Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N := by
  set S := saddleShellDerivativeOne ε with hS
  set a := Real.exp (Real.log Real.pi / 2 + S) with ha
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have ha2 : a ^ 2 = Real.pi * Real.exp (2 * S) := by
    rw [ha, sq, ← Real.exp_add,
      show (Real.log Real.pi / 2 + S) + (Real.log Real.pi / 2 + S) = Real.log Real.pi + 2 * S by ring,
      Real.exp_add, Real.exp_log Real.pi_pos]
  have hV : saddleSmallRadiusVariable ε r = (a * r) ^ 2 := by
    unfold saddleSmallRadiusVariable; rw [mul_pow, ha2]
  rw [hV, Real.sqrt_sq (mul_nonneg ha0 hr), Real.exp_nat_mul]
  ring

