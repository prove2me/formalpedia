-- Prove2me | solution 2 for CohnElkies.abs_lowerEndpointPhase_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:57:07.171817+00:00
-- url     : https://prove2.me/submissions/a300a024-fed8-4a58-923d-8bba1d4c0602

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


theorem solution (T : ℝ) :
    |lowerEndpointPhase T| ≤ Real.pi * |T| + T ^ 2 := by
  unfold lowerEndpointPhase
  have ha := abs_nonneg T
  have h1 : Real.arctan (|T|/2) < Real.pi/2 := Real.arctan_lt_pi_div_two _
  have h2 : 0 ≤ Real.arctan (|T|/2) := Real.arctan_nonneg.mpr (by positivity)
  have h3 : Real.log (1 + T^2/4) ≤ T^2/4 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + T^2/4 by positivity); linarith
  have h4 : 0 ≤ Real.log (1 + T^2/4) := Real.log_nonneg (by nlinarith [sq_nonneg T])
  have hp := Real.pi_pos
  have h5 : |T|/2 * Real.arctan (|T|/2) ≤ |T|/2 * (Real.pi/2) := by
    apply mul_le_mul_of_nonneg_left h1.le (by positivity)
  have h6 : 0 ≤ |T|/2 * Real.arctan (|T|/2) := by positivity
  have hT : T^2 = |T|^2 := (sq_abs T).symm
  rw [abs_le]; constructor <;> nlinarith

