-- Prove2me | solution 2 for CohnElkies.saddleExpSeries_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:03:59.747804+00:00
-- url     : https://prove2.me/submissions/311d6392-15a2-4224-b52c-147001fab83f

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


theorem solution (y : ℝ) :
    HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ))
      (Real.exp y) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp y

