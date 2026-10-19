-- Prove2me | solution 2 for CohnElkies.saddle_log_sq_le_four_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:55:48.879135+00:00
-- url     : https://prove2.me/submissions/e7627c5e-4cb2-4a47-975c-45279c3a8bfb

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


theorem solution
    {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 4 * x := by
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have h1 : Real.log x ≤ 2 * Real.sqrt x := by
    have := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt (by linarith)] at this
    linarith
  calc Real.log x ^ 2 ≤ (2 * Real.sqrt x) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 4 * x := by rw [mul_pow, Real.sq_sqrt (by linarith)]; ring

