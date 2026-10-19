-- Prove2me | solution 2 for CohnElkies.inv_cosh_le_two_exp_neg_abs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:58:37.846697+00:00
-- url     : https://prove2.me/submissions/94073331-5fdf-4f06-a5df-e797da534c4b

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
    (Real.cosh u)⁻¹ ≤ 2 * Real.exp (-|u|) := by
  have hc : Real.cosh u = Real.cosh |u| := (Real.cosh_abs u).symm
  rw [hc, Real.cosh_eq]
  have h1 : 0 < Real.exp |u| := Real.exp_pos _
  have h2 : 0 < Real.exp (-|u|) := Real.exp_pos _
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  have : Real.exp (-|u|) * Real.exp |u| = 1 := by rw [← Real.exp_add]; simp
  nlinarith

