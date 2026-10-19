-- Prove2me | solution 2 for CohnElkies.norm_complexLaplaceKernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:09:32.041857+00:00
-- url     : https://prove2.me/submissions/f71f3cf1-0a04-4a85-92f7-adab688bf026

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution (z : ℂ) (x : ℝ) :
    ‖Complex.exp (-z * (x : ℂ))‖ =
      Real.exp (-z.re * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp

