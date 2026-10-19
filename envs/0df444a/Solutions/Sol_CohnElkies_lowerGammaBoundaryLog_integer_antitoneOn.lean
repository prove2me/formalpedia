-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_integer_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/d1a7be03-f224-491a-8c4b-3a18f2af185d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    (k : ℕ) (R : ℝ) :
    AntitoneOn (lowerGammaBoundaryLog (k : ℝ) R)
      (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  rw [lowerGammaBoundaryLog_integer k R hy.ne',
    lowerGammaBoundaryLog_integer k R hx.ne']
  have hsum :
      (∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt ((j : ℝ) ^ 2 + (x / 2) ^ 2))) ≤
      ∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hradx : 0 < (j : ℝ) ^ 2 + (x / 2) ^ 2 := by
      nlinarith [sq_nonneg (j : ℝ), sq_pos_of_pos (half_pos hx)]
    apply Real.log_le_log (Real.sqrt_pos.mpr hradx)
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (y / 2 - x / 2),
      mul_nonneg (half_pos hx).le
        (show 0 ≤ y / 2 - x / 2 by linarith)]
  linarith
end CohnElkies
