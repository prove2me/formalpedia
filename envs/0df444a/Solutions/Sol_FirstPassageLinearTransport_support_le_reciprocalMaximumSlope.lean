-- Prove2me | solution 1 for FirstPassageLinearTransport.support_le_reciprocalMaximumSlope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:54.675027+00:00
-- url     : https://prove2.me/submissions/513e3121-cf71-48e0-b4db-bdc1ad62e979

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_add_reciprocalMaximumEpsilon
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_one_eq_exp_incrementSum
import Theorems.Thm_FirstPassageLinearTransport_log_ballotWordValue_one
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


attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {u : ℝ} (hu : 1 ≤ u) {r : ℕ}
    (hlog : Real.log u ≤
      reciprocalMaximumEpsilon * (r : ℝ) * Real.log 3)
    (v : Fin r → Bool) (hv : ballotWordValue 1 v ≤ u) :
    ((boolSupport v).card : ℝ) ≤
      (3 / 4 - reciprocalMaximumEpsilon) * r := by
  have huPos : 0 < u := zero_lt_one.trans_le hu
  have hvalPos : 0 < ballotWordValue 1 v := by
    rw [ballotWordValue_one_eq_exp_incrementSum]
    exact Real.exp_pos _
  have hlogle : Real.log (ballotWordValue 1 v) ≤ Real.log u :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hvalPos) (Set.mem_Ioi.mpr huPos) hv
  rw [log_ballotWordValue_one] at hlogle
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have htilt : collatzTilt * Real.log 3 = Real.log 2 := by
    unfold collatzTilt
    field_simp [ne_of_gt hlog3]
  have hmul : ((boolSupport v).card : ℝ) * Real.log 3 ≤
      (collatzTilt + reciprocalMaximumEpsilon) *
        (r : ℝ) * Real.log 3 := by
    calc
      ((boolSupport v).card : ℝ) * Real.log 3 ≤
          (r : ℝ) * Real.log 2 +
            reciprocalMaximumEpsilon * (r : ℝ) * Real.log 3 := by
        linarith
      _ = (collatzTilt + reciprocalMaximumEpsilon) *
          (r : ℝ) * Real.log 3 := by
        rw [← htilt]
        ring
  have hslope : ((boolSupport v).card : ℝ) ≤
      (collatzTilt + reciprocalMaximumEpsilon) * (r : ℝ) := by
    exact le_of_mul_le_mul_right (by
      simpa [mul_assoc] using hmul) hlog3
  rw [collatzTilt_add_reciprocalMaximumEpsilon] at hslope
  exact hslope
end FirstPassageLinearTransport
