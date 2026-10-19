-- Prove2me | solution 2 for CohnElkies.saddleExpSeries_firstMoment_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:03:45.077604+00:00
-- url     : https://prove2.me/submissions/e405c604-1d69-4de1-b11a-f3fa543c3b6d

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
    HasSum
      (fun n : ℕ => (n : ℝ) *
        (y ^ n / (n.factorial : ℝ)))
      (y * Real.exp y) := by
  have h0 : HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp y
  have h1 := h0.mul_left y
  have h2 : HasSum (fun n : ℕ => ((n+1 : ℕ) : ℝ) * (y ^ (n+1) / ((n+1).factorial : ℝ)))
      (y * Real.exp y) := by
    have e : (fun n : ℕ => ((n+1 : ℕ) : ℝ) * (y ^ (n+1) / ((n+1).factorial : ℝ))) =
        fun n => y * (y ^ n / (n.factorial : ℝ)) := by
      funext n; rw [Nat.factorial_succ, pow_succ]; push_cast; field_simp
    rw [e]; exact h1
  refine (hasSum_nat_add_iff' 1).mp ?_
  simpa using h2

