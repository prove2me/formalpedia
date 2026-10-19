-- Prove2me | solution 1 for CohnElkies.saddleGaussianTailWeight_le_two_exp_three_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/4b201769-a0b5-4418-953e-13ff7b153e1e

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
namespace CohnElkies
theorem _root_.solution (T : ℝ) :
    saddleGaussianTailWeight T ≤
      2 * Real.exp (3 * |T|) := by
  have hlinear : |T| ≤ Real.exp |T| := by
    calc
      |T| ≤ 1 + |T| := by linarith
      _ ≤ Real.exp |T| := by
        simpa [add_comm] using! Real.add_one_le_exp |T|
  have hcube : |T| ^ 3 ≤ (Real.exp |T|) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg T) hlinear 3
  have hexpcube : (Real.exp |T|) ^ 3 =
      Real.exp (3 * |T|) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hone : 1 ≤ Real.exp (3 * |T|) := by
    exact (Real.one_le_exp_iff).mpr (by positivity)
  unfold saddleGaussianTailWeight
  rw [hexpcube] at hcube
  linarith
end CohnElkies
