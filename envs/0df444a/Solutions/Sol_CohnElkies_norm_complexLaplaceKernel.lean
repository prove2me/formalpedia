-- Prove2me | solution 1 for CohnElkies.norm_complexLaplaceKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/3c0d47df-c010-4f8c-8b2a-ba3007456123

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
namespace CohnElkies
theorem _root_.solution (z : ℂ) (x : ℝ) :
    ‖Complex.exp (-z * (x : ℂ))‖ =
      Real.exp (-z.re * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]
end CohnElkies
