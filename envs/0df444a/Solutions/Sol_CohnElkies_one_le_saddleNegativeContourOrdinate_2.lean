-- Prove2me | solution 2 for CohnElkies.one_le_saddleNegativeContourOrdinate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:45.875531+00:00
-- url     : https://prove2.me/submissions/a90eb12c-8508-4023-8231-7aed125e9bd5

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    1 ≤ saddleNegativeContourOrdinate ℓ N := by
  unfold saddleNegativeContourOrdinate
  have : 0 ≤ (2 * (N : ℝ) + 1) / ℓ := by positivity
  linarith

