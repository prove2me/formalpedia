-- Prove2me | solution 2 for CohnElkies.saddleSmallRadiusVariable_neg_pow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:09:16.672135+00:00
-- url     : https://prove2.me/submissions/4b5835b1-26dd-4d9c-ab24-5037e11d64f7

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


theorem solution
    (ε r : ℝ) (n : ℕ) :
    (-saddleSmallRadiusVariable ε r) ^ n =
      (-1 : ℝ) ^ n * Real.pi ^ n *
        Real.exp (2 * saddleShellDerivativeOne ε) ^ n *
          r ^ (2 * n) := by
  unfold saddleSmallRadiusVariable
  rw [pow_mul]
  ring

