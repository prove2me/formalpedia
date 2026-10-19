-- Prove2me | solution 2 for CohnElkies.upperShortMargin_mul_exp_le_zero_value
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:57:41.521176+00:00
-- url     : https://prove2.me/submissions/cf7be74e-4e11-4b07-993e-893ce1dcc699

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
    {ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) :
    shortMargin ε a * Real.exp (ε * a) ≤
      1 - 10 * ε := by
  unfold shortMargin
  have ht : 0 ≤ ε * a := mul_nonneg hε.le ha
  set t := ε * a with htdef
  have hE1 : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hE2 : (1 - t) * Real.exp t ≤ 1 := by
    have h := Real.add_one_le_exp (-t)
    have : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos t]
  have e : 1 - 10 * ε * (1 + a) = 1 - 10 * ε - 10 * t := by rw [htdef]; ring
  rw [e]
  nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hE1), mul_nonneg ht (Real.exp_pos t).le]

