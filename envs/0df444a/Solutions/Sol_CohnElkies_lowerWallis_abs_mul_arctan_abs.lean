-- Prove2me | solution 1 for CohnElkies.lowerWallis_abs_mul_arctan_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/e21132bd-3531-4e98-b79d-f2ba2c5ea890

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (u : ℝ) :
    |u| * Real.arctan |u| = u * Real.arctan u := by
  by_cases hu : 0 ≤ u
  · simp [abs_of_nonneg hu]
  · have hnegative : u < 0 := lt_of_not_ge hu
    rw [abs_of_neg hnegative, Real.arctan_neg]
    ring
end CohnElkies
