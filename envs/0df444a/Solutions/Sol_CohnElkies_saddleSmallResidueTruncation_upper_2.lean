-- Prove2me | solution 2 for CohnElkies.saddleSmallResidueTruncation_upper
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:06.010769+00:00
-- url     : https://prove2.me/submissions/619d72b1-d021-40c4-a403-8bfa72464a63

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
    {ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    (saddleSmallResidueTruncation ℓ : ℝ) ≤
      20 * Real.log ℓ + 1 := by
  unfold saddleSmallResidueTruncation
  have : 0 ≤ 20 * Real.log ℓ := by have := Real.log_nonneg hℓ; linarith
  exact (Nat.ceil_lt_add_one this).le

