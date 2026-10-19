-- Prove2me | solution 2 for CohnElkies.saddleExpSeries_secondFallingMoment_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:18:38.857428+00:00
-- url     : https://prove2.me/submissions/a3ed43dc-4455-412f-87b6-5c5931554389

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
      (fun n : ℕ =>
        (n : ℝ) * ((n : ℝ) - 1) *
          (y ^ n / (n.factorial : ℝ)))
      (y ^ 2 * Real.exp y) := by
  have hexp : HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp y
  rw [← hasSum_nat_add_iff' 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  have := hexp.mul_left (y ^ 2)
  refine this.congr_fun ?_
  intro n
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

