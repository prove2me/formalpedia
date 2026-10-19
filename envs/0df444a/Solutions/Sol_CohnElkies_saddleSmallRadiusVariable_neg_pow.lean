-- Prove2me | solution 1 for CohnElkies.saddleSmallRadiusVariable_neg_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/766a4e75-0f96-4ab5-931b-ea32f2698275

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (ε r : ℝ) (n : ℕ) :
    (-saddleSmallRadiusVariable ε r) ^ n =
      (-1 : ℝ) ^ n * Real.pi ^ n *
        Real.exp (2 * saddleShellDerivativeOne ε) ^ n *
          r ^ (2 * n) := by
  calc
    (-saddleSmallRadiusVariable ε r) ^ n =
        ((-1 : ℝ) * Real.pi *
          Real.exp (2 * saddleShellDerivativeOne ε) *
            r ^ 2) ^ n := by
              congr 1
              unfold saddleSmallRadiusVariable
              ring
    _ = (-1 : ℝ) ^ n * Real.pi ^ n *
          Real.exp (2 * saddleShellDerivativeOne ε) ^ n *
            (r ^ 2) ^ n := by
              simp only [mul_pow]
    _ = (-1 : ℝ) ^ n * Real.pi ^ n *
          Real.exp (2 * saddleShellDerivativeOne ε) ^ n *
            r ^ (2 * n) := by
              rw [← pow_mul]
end CohnElkies
