-- Prove2me | solution 1 for CohnElkies.lowerWallis_norm_one_sub_I_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/933b690e-fe6d-4644-bea6-42fea5ecd017

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
    ‖1 - Complex.I * (u : ℂ)‖ =
      Real.sqrt (1 + u ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring
end CohnElkies
