-- Prove2me | solution 2 for CohnElkies.upper_one_sub_cos_quadratic_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:55:15.19947+00:00
-- url     : https://prove2.me/submissions/62713015-e5b0-46aa-be0a-28fd83a2cf51

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
    {x : ℝ} (hx : |x| ≤ 1) :
    x ^ 2 / 4 ≤ 1 - Real.cos x := by
  have h := Real.cos_bound hx
  have h2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  have h4 : |x| ^ 4 = (x^2)^2 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, sq_abs]
  rw [h4] at h
  have := (abs_le.mp h).2
  nlinarith [sq_nonneg x]

