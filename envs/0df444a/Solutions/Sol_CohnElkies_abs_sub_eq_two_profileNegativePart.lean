-- Prove2me | solution 1 for CohnElkies.abs_sub_eq_two_profileNegativePart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/6d34ef03-b5eb-439a-bd8b-ff6b25e966e1

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
namespace CohnElkies
theorem _root_.solution (φ : ℝ → ℝ) (v : ℝ) :
    |φ v| - φ v = 2 * profileNegativePart φ v := by
  unfold profileNegativePart
  rcases le_total 0 (φ v) with h | h
  · rw [abs_of_nonneg h, max_eq_right (by linarith)]
    ring
  · rw [abs_of_nonpos h, max_eq_left (by linarith)]
    ring
end CohnElkies
