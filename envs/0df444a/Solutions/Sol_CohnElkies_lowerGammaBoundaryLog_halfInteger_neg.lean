-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_halfInteger_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/bccfb340-7086-4b99-beed-1a564538d926

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger

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
    (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R (-y) =
      lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y := by
  rw [lowerGammaBoundaryLog_halfInteger k R (neg_ne_zero.mpr hy),
    lowerGammaBoundaryLog_halfInteger k R hy]
  simp [div_pow]
end CohnElkies
