-- Prove2me | solution 1 for CohnElkies.saddleSmallRadiusVariable_halfIntegerFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/a9293c6a-0944-4e63-b380-1f068633ea90

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSmallRadiusVariable_sqrt_eq_source

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    (ε : ℝ) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    r ^ (2 * N + 1) *
      Real.exp
        (((2 * N + 1 : ℕ) : ℝ) *
          (Real.log Real.pi / 2 +
            saddleShellDerivativeOne ε)) =
      Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N := by
  let q : ℝ := r * Real.exp
    (Real.log Real.pi / 2 + saddleShellDerivativeOne ε)
  have hsqrt := saddleSmallRadiusVariable_sqrt_eq_source ε hr
  have hq : q ^ 2 = saddleSmallRadiusVariable ε r := by
    have he :
        Real.exp
          (Real.log Real.pi / 2 + saddleShellDerivativeOne ε) ^ 2 =
          Real.pi * Real.exp (2 * saddleShellDerivativeOne ε) := by
      rw [pow_two, ← Real.exp_add]
      rw [show
        (Real.log Real.pi / 2 + saddleShellDerivativeOne ε) +
            (Real.log Real.pi / 2 + saddleShellDerivativeOne ε) =
          Real.log Real.pi + 2 * saddleShellDerivativeOne ε by ring,
        Real.exp_add, Real.exp_log Real.pi_pos]
    try dsimp [q]
    rw [mul_pow, he]
    unfold saddleSmallRadiusVariable
    ring
  rw [Real.exp_nat_mul]
  rw [← mul_pow]
  change q ^ (2 * N + 1) =
    Real.sqrt (saddleSmallRadiusVariable ε r) *
      saddleSmallRadiusVariable ε r ^ N
  rw [hsqrt, ← hq]
  change q ^ (2 * N + 1) = q * (q ^ 2) ^ N
  rw [← pow_mul, pow_succ]
  ring
end CohnElkies
