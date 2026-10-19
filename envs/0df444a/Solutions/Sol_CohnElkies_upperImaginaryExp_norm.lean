-- Prove2me | solution 1 for CohnElkies.upperImaginaryExp_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/a7c52df2-f84b-4eff-a3b3-994d621f9e09

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution (x : ℝ) :
    ‖upperImaginaryExp x‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal x
end CohnElkies
