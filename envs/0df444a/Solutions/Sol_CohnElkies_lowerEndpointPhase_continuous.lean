-- Prove2me | solution 1 for CohnElkies.lowerEndpointPhase_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/85dc5fda-bb2e-4def-b6d7-5267a35b3a6a

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
theorem _root_.solution :
    Continuous lowerEndpointPhase := by
  have hargument : Continuous
      (fun T : ℝ => 1 + T ^ 2 / 4) := by
    fun_prop
  have hlog : Continuous
      (fun T : ℝ => Real.log (1 + T ^ 2 / 4)) :=
    hargument.log (fun T => by
      have hsq : 0 ≤ T ^ 2 := sq_nonneg T
      positivity)
  have hfirst : Continuous
      (fun T : ℝ => -Real.pi * |T| / 4) := by
    fun_prop
  have hsecond : Continuous
      (fun T : ℝ =>
        (1 / 2 : ℝ) * Real.log (1 + T ^ 2 / 4)) :=
    continuous_const.mul hlog
  have hthird : Continuous
      (fun T : ℝ =>
        |T| / 2 * Real.arctan (|T| / 2)) :=
    (continuous_abs.div_const 2).mul
      (Real.continuous_arctan.comp
        (continuous_abs.div_const 2))
  exact (hfirst.sub hsecond).add hthird
end CohnElkies
