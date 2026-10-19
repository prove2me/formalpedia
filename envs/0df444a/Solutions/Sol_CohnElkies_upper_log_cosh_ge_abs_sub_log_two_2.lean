-- Prove2me | solution 2 for CohnElkies.upper_log_cosh_ge_abs_sub_log_two
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:02:44.916816+00:00
-- url     : https://prove2.me/submissions/cb0ee644-b19d-4c30-b054-555be0a72dda

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


theorem solution (x : ℝ) :
    |x| - Real.log 2 ≤ Real.log (Real.cosh x) := by
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  have h2 : Real.exp |x| / 2 ≤ Real.cosh x := by
    rw [Real.cosh_eq]
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      · have := Real.exp_pos x; have := Real.exp_pos (-x); simp; linarith
  have := Real.log_le_log (by positivity) h2
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at this
  linarith

