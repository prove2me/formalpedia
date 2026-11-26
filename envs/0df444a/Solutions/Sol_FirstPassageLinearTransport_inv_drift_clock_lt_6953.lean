-- Prove2me | solution 1 for FirstPassageLinearTransport.inv_drift_clock_lt_6953
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:58:17.832817+00:00
-- url     : https://prove2.me/submissions/608775d5-aed0-4926-b5d5-5fb7fc864e76

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum.BigOperators
import Definitions.Def_FirstPassageLinearTransport_Scalar
import Definitions.Def_FirstPassageLinearTransport_Constants
import Theorems.Thm_FirstPassageLinearTransport_log_four_thirds_gt_296_div_1029
import Theorems.Thm_FirstPassageLinearTransport_inv_drift_clock_eq

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    1 / ((1 - a0) * Real.log 2) < (6953 / 1000 : ℝ) := by
  rw [inv_drift_clock_eq]
  have hlog := log_four_thirds_gt_296_div_1029
  have hlogPos : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  apply (div_lt_iff₀ hlogPos).2
  have hrat : (2 : ℝ) < (6953 / 1000 : ℝ) * (296 / 1029) := by
    norm_num
  exact hrat.trans (mul_lt_mul_of_pos_left hlog (by norm_num))
end FirstPassageLinearTransport
