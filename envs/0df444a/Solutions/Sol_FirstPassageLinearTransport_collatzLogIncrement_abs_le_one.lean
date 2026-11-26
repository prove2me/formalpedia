-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzLogIncrement_abs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:29:22.993799+00:00
-- url     : https://prove2.me/submissions/c8c19d58-8b6a-460d-8f0a-43e3ae5b440b

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (b : Bool) :
    |collatzLogIncrement b| ≤ 1 := by
  cases b with
  | false =>
      simp only [collatzLogIncrement, Bool.false_eq_true, if_false, abs_neg]
      rw [abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
      have h := Real.log_lt_sub_one_of_pos
        (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
      norm_num at h
      exact h.le
  | true =>
      have hpos : 0 < Real.log 3 - Real.log 2 := by
        exact sub_pos.mpr (Real.strictMonoOn_log
          (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
          (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 3))
          (by norm_num))
      simp only [collatzLogIncrement, if_true]
      rw [abs_of_pos hpos]
      have hdiv : Real.log 3 - Real.log 2 = Real.log (3 / 2 : ℝ) := by
        rw [Real.log_div (by norm_num) (by norm_num)]
      rw [hdiv]
      linarith [Real.log_lt_sub_one_of_pos
        (by norm_num : (0 : ℝ) < 3 / 2)
        (by norm_num : (3 / 2 : ℝ) ≠ 1)]
end FirstPassageLinearTransport
