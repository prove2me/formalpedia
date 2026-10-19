-- Prove2me | solution 2 for CohnElkies.lowerWallis_abs_mul_arctan_abs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:25:03.136986+00:00
-- url     : https://prove2.me/submissions/03a16196-a171-4e91-8170-ab416868ac66

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


theorem solution (u : ℝ) :
    |u| * Real.arctan |u| = u * Real.arctan u := by
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, Real.arctan_neg]; ring

