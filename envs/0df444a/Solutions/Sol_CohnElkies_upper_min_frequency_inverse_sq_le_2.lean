-- Prove2me | solution 2 for CohnElkies.upper_min_frequency_inverse_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:14:49.931986+00:00
-- url     : https://prove2.me/submissions/29383b91-56c0-43d1-99fd-0768048d171d

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
    min (T ^ 2) ((a ^ 2)⁻¹) ≤
      min (T ^ 2) 1 * (1 + (a ^ 2)⁻¹) := by
  have hb : 0 ≤ (a ^ 2)⁻¹ := by positivity
  rcases le_total (T ^ 2) 1 with h | h
  · rw [min_eq_left h]
    have := min_le_left (T ^ 2) ((a ^ 2)⁻¹)
    nlinarith [sq_nonneg T]
  · rw [min_eq_right h]
    have := min_le_right (T ^ 2) ((a ^ 2)⁻¹)
    linarith

