-- Prove2me | solution 2 for CohnElkies.exists_saddleSource_central_error_tolerance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:13:21.331249+00:00
-- url     : https://prove2.me/submissions/5703a64b-8469-4acf-9050-9d4445bfc101

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧
      2 * q + (1 + 2 * q) * q < κ := by
  refine ⟨min 1 (κ / 6), lt_min one_pos (by linarith), min_le_left _ _, ?_⟩
  have h1 := min_le_left 1 (κ / 6)
  have h2 := min_le_right 1 (κ / 6)
  have h3 : 0 < min 1 (κ / 6) := lt_min one_pos (by linarith)
  nlinarith

