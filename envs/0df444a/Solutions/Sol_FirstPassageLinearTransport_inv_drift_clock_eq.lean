-- Prove2me | solution 1 for FirstPassageLinearTransport.inv_drift_clock_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:35:33.43885+00:00
-- url     : https://prove2.me/submissions/1a887e81-04ca-4b17-bf29-52399add7167

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum.BigOperators
import Definitions.Def_FirstPassageLinearTransport_Scalar
import Definitions.Def_FirstPassageLinearTransport_Constants
import Theorems.Thm_FirstPassageLinearTransport_a0_lt_one


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    1 / ((1 - a0) * Real.log 2) = 2 / Real.log (4 / 3) := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog3 : Real.log 3 = logTwoThree * Real.log 2 := by
    unfold logTwoThree
    field_simp
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have h43 : Real.log (4 / 3) = 2 * ((1 - a0) * Real.log 2) := by
    rw [Real.log_div (by norm_num) (by norm_num), hlog4, hlog3]
    unfold a0
    ring
  rw [h43]
  have hA : (1 - a0) * Real.log 2 ≠ 0 :=
    ne_of_gt (mul_pos (sub_pos.mpr a0_lt_one) (Real.log_pos (by norm_num)))
  field_simp [hA]
end FirstPassageLinearTransport
