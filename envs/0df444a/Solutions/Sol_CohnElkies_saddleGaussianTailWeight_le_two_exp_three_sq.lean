-- Prove2me | solution 1 for CohnElkies.saddleGaussianTailWeight_le_two_exp_three_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/59ed188b-3f05-4e24-a1c5-1882f8354e4c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddle_abs_le_exp_sq

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
      2 * Real.exp (3 * T ^ 2) := by
  have habs := saddle_abs_le_exp_sq T
  have hcube : |T| ^ 3 ≤ (Real.exp (T ^ 2)) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg T) habs 3
  have hexpcube : (Real.exp (T ^ 2)) ^ 3 =
      Real.exp (3 * T ^ 2) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hone : 1 ≤ Real.exp (3 * T ^ 2) := by
    exact (Real.one_le_exp_iff).mpr (by positivity)
  unfold saddleGaussianTailWeight
  rw [hexpcube] at hcube
  linarith
end CohnElkies
