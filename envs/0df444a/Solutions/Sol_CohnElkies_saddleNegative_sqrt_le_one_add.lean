-- Prove2me | solution 1 for CohnElkies.saddleNegative_sqrt_le_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/29fe7829-eb63-4f79-a248-54a3f0b1b588

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {y : ℝ} (hy : 0 ≤ y) :
    Real.sqrt y ≤ 1 + y := by
  have hs := Real.sqrt_nonneg y
  have hsq := Real.sq_sqrt hy
  nlinarith [sq_nonneg (Real.sqrt y - 1)]
end CohnElkies
