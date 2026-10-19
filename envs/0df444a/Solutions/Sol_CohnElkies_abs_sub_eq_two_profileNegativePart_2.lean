-- Prove2me | solution 2 for CohnElkies.abs_sub_eq_two_profileNegativePart
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:57:44.857724+00:00
-- url     : https://prove2.me/submissions/f840fe43-0e4d-455d-865f-c739b7bc2571

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution (φ : ℝ → ℝ) (v : ℝ) :
    |φ v| - φ v = 2 * profileNegativePart φ v := by
  unfold profileNegativePart
  rcases le_total 0 (φ v) with h | h
  · rw [abs_of_nonneg h, max_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_left (by linarith)]; ring

