-- Prove2me | solution 2 for CohnElkies.saddleGaussianTailWeight_le_two_exp_three_sq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:38.708935+00:00
-- url     : https://prove2.me/submissions/5c759db7-2ac7-4f28-8ee8-e2f5821d2fde

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology


theorem solution (T : ℝ) :
    saddleGaussianTailWeight T ≤
      2 * Real.exp (3 * T ^ 2) := by
  unfold saddleGaussianTailWeight
  have h := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 3 * T ^ 2 by positivity)
  have ht : 0 ≤ |T| := abs_nonneg T
  have hsq : T ^ 2 = |T| ^ 2 := (sq_abs T).symm
  rw [hsq] at h ⊢
  nlinarith [sq_nonneg (|T| - 1), sq_nonneg |T|, mul_nonneg ht (sq_nonneg (|T| - 1))]

