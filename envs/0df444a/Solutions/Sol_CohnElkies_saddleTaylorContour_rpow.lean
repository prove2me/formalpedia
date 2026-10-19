-- Prove2me | solution 1 for CohnElkies.saddleTaylorContour_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/a4442c3d-b72e-4999-90ef-b60d869e7012

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    (r : ℝ) (N : ℕ) :
    r ^ (-(saddleTaylorContour N)) =
      r ^ (2 * N + 1) := by
  unfold saddleTaylorContour
  rw [neg_neg, Real.rpow_natCast]
end CohnElkies
