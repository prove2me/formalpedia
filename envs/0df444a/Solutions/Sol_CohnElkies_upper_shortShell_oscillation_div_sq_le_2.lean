-- Prove2me | solution 2 for CohnElkies.upper_shortShell_oscillation_div_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:07.112528+00:00
-- url     : https://prove2.me/submissions/955ea172-1eb0-4d08-9d6d-16d16ba5a3d1

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
    {a : ℝ} (ha : 0 < a) (T : ℝ) :
    (1 - Real.cos (a * T)) / (2 * a ^ 2) ≤
      min (T ^ 2) ((a ^ 2)⁻¹) := by
  have h1 := Real.one_sub_sq_div_two_le_cos (x := a * T)
  have h2 := Real.neg_one_le_cos (a * T)
  have ha2 : 0 < a ^ 2 := by positivity
  apply le_min
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg T, sq_nonneg (a * T)]
  · rw [div_le_iff₀ (by positivity)]
    have : (a ^ 2)⁻¹ * (2 * a ^ 2) = 2 := by field_simp
    rw [this]; linarith

