-- Prove2me | solution 1 for CohnElkies.abs_lowerEndpointPhase_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/2d12e34c-53de-4ecd-95b6-980ef8abc061

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
theorem _root_.solution (T : ℝ) :
    |lowerEndpointPhase T| ≤ Real.pi * |T| + T ^ 2 := by
  have hnonneg : 0 ≤ T ^ 2 / 4 := by positivity
  have hlogzero : 0 ≤ Real.log (1 + T ^ 2 / 4) :=
    Real.log_nonneg (by linarith)
  have hlogupper :
      Real.log (1 + T ^ 2 / 4) ≤ T ^ 2 / 4 := by
    have h := Real.log_le_sub_one_of_pos
      (show 0 < 1 + T ^ 2 / 4 by positivity)
    linarith
  have hatanzero : 0 ≤ Real.arctan (|T| / 2) :=
    Real.arctan_nonneg.mpr (by positivity)
  have hatanupper : Real.arctan (|T| / 2) ≤ Real.pi / 2 :=
    (Real.arctan_lt_pi_div_two _).le
  have hmulzero :
      0 ≤ |T| / 2 * Real.arctan (|T| / 2) :=
    mul_nonneg (by positivity) hatanzero
  have hmulupper :
      |T| / 2 * Real.arctan (|T| / 2) ≤
        |T| / 2 * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_left hatanupper (by positivity)
  have hpimagnitude : 0 ≤ Real.pi * |T| :=
    mul_nonneg Real.pi_pos.le (abs_nonneg T)
  unfold lowerEndpointPhase
  apply (abs_le).2
  constructor
  · nlinarith [sq_nonneg T]
  · nlinarith [sq_nonneg T]
end CohnElkies
