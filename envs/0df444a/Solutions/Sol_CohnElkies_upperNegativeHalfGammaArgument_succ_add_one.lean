-- Prove2me | solution 1 for CohnElkies.upperNegativeHalfGammaArgument_succ_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/500ecd6d-8925-4aa0-babf-37d2e4256a57

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
theorem _root_.solution
    (N : ℕ) (s : ℝ) :
    upperNegativeHalfGammaArgument (N + 1) s + 1 =
      upperNegativeHalfGammaArgument N s := by
  unfold upperNegativeHalfGammaArgument
  simp only [Nat.cast_add, Nat.cast_one]
  ring
end CohnElkies
