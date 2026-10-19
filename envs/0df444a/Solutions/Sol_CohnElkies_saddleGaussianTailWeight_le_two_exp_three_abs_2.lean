-- Prove2me | solution 2 for CohnElkies.saddleGaussianTailWeight_le_two_exp_three_abs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:55:54.921204+00:00
-- url     : https://prove2.me/submissions/5ff3360b-c642-4cee-817b-457e64f36822

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
      2 * Real.exp (3 * |T|) := by
  unfold saddleGaussianTailWeight
  have ht : 0 ≤ |T| := abs_nonneg T
  have h1 := Real.pow_div_factorial_le_exp (x := 3 * |T|) (by positivity) 3
  have h2 : (1:ℝ) ≤ Real.exp (3 * |T|) := Real.one_le_exp (by positivity)
  norm_num [Nat.factorial] at h1
  nlinarith [pow_nonneg ht 3]

