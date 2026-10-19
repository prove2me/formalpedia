-- Prove2me | solution 1 for CohnElkies.saddleSmallRadiusVariable_sqrt_eq_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/3d2a79fb-a2f4-49ed-8ea6-152e79b89d71

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSmallRadiusVariable_nonneg

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
    (ε : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt (saddleSmallRadiusVariable ε r) =
      r * Real.exp
        (Real.log Real.pi / 2 + saddleShellDerivativeOne ε) := by
  let q : ℝ := r * Real.exp
    (Real.log Real.pi / 2 + saddleShellDerivativeOne ε)
  have hq : 0 ≤ q := by
    try dsimp [q]
    positivity
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
  have hsq : q ^ 2 = saddleSmallRadiusVariable ε r := by
    try dsimp [q]
    rw [mul_pow, he]
    unfold saddleSmallRadiusVariable
    ring
  have hsqrt := Real.sq_sqrt
    (saddleSmallRadiusVariable_nonneg ε r)
  have hsqrtpos := Real.sqrt_nonneg
    (saddleSmallRadiusVariable ε r)
  change Real.sqrt (saddleSmallRadiusVariable ε r) = q
  nlinarith
end CohnElkies
