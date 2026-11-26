-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzTiltVariance_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:29:03.832189+00:00
-- url     : https://prove2.me/submissions/68bbe141-0759-40b3-84a9-ccf4fcae1c23

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_pos
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_lt_one
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
theorem _root_.solution : 0 < collatzTiltVariance := by
  have hp0 := collatzTilt_pos
  have hp1 := collatzTilt_lt_one
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold collatzTiltVariance bernoulliAverage collatzLogIncrement
  simp only [Bool.false_eq_true, if_false, if_true]
  have hlog2ne : -Real.log 2 ≠ 0 := neg_ne_zero.mpr hlog2.ne'
  have hfirst : 0 < (1 - collatzTilt) * (-Real.log 2) ^ 2 :=
    mul_pos (sub_pos.mpr hp1) (sq_pos_of_ne_zero hlog2ne)
  have hsecond : 0 ≤ collatzTilt * (Real.log 3 - Real.log 2) ^ 2 :=
    mul_nonneg hp0.le (sq_nonneg _)
  linarith
end FirstPassageLinearTransport
