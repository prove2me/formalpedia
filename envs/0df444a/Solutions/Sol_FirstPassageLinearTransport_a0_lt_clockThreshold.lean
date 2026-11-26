-- Prove2me | solution 1 for FirstPassageLinearTransport.a0_lt_clockThreshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:58:56.570851+00:00
-- url     : https://prove2.me/submissions/600d4512-35c1-43ad-a2e3-fb628f170d87

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum.BigOperators
import Definitions.Def_FirstPassageLinearTransport_Scalar
import Definitions.Def_FirstPassageLinearTransport_Constants
import Theorems.Thm_FirstPassageLinearTransport_inv_drift_clock_lt_6953
import Theorems.Thm_FirstPassageLinearTransport_a0_lt_one


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    a0 < 1 - 1 / ((6953 / 1000 : ℝ) * Real.log 2) := by
  have hden : 0 < (6953 / 1000 : ℝ) * Real.log 2 := by positivity
  have hdrift : 0 < (1 - a0) * Real.log 2 := by
    exact mul_pos (sub_pos.mpr a0_lt_one) (Real.log_pos (by norm_num))
  have h := inv_drift_clock_lt_6953
  rw [div_lt_iff₀ hdrift] at h
  have hinv : 1 / ((6953 / 1000 : ℝ) * Real.log 2) < 1 - a0 := by
    apply (div_lt_iff₀ hden).2
    convert h using 1
    all_goals ring
  linarith
end FirstPassageLinearTransport
