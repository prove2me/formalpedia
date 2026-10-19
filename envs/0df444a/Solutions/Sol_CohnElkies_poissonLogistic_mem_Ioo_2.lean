-- Prove2me | solution 2 for CohnElkies.poissonLogistic_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:55:29.961774+00:00
-- url     : https://prove2.me/submissions/9ebdd8a8-af2a-4a0d-9828-c42d3fe29fa2

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
    poissonLogistic u ∈ Ioo (0 : ℝ) 1 := by
  unfold poissonLogistic
  have h := Real.exp_pos (Real.pi * u)
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]; linarith

