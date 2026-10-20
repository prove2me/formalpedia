-- Prove2me | solution 2 for CohnElkies.saddleNegative_sqrt_le_one_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:31:51.639502+00:00
-- url     : https://prove2.me/submissions/22e6d1d0-c6fa-41dc-9cc1-9b14a225b9cc

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


theorem solution
    {y : ℝ} (hy : 0 ≤ y) :
    Real.sqrt y ≤ 1 + y := by
  nlinarith [Real.sq_sqrt hy, Real.sqrt_nonneg y, sq_nonneg (Real.sqrt y - 1)]

