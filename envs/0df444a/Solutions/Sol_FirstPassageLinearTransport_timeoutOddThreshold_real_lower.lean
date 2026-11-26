-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutOddThreshold_real_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:07:36.903577+00:00
-- url     : https://prove2.me/submissions/7ab6fb8f-3d34-46eb-bcb5-f0575d4cfd03

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_two_pow_lt_three_pow_timeoutOddThreshold_succ
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (q : ℕ) :
    (q : ℝ) * logThreeTwo - 1 < (timeoutOddThreshold q : ℝ) := by
  have hpowNat := two_pow_lt_three_pow_timeoutOddThreshold_succ q
  have hpow :
      (2 : ℝ) ^ q < (3 : ℝ) ^ (timeoutOddThreshold q + 1) := by
    exact_mod_cast hpowNat
  have hlog := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (show (0 : ℝ) < (2 : ℝ) ^ q by positivity))
    (Set.mem_Ioi.mpr
      (show (0 : ℝ) < (3 : ℝ) ^ (timeoutOddThreshold q + 1) by positivity))
    hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold logThreeTwo
  have hratio :
      (q : ℝ) * (Real.log 2 / Real.log 3) <
        (timeoutOddThreshold q : ℝ) + 1 := by
    rw [div_eq_mul_inv]
    rw [show (q : ℝ) * (Real.log 2 * (Real.log 3)⁻¹) =
        ((q : ℝ) * Real.log 2) / Real.log 3 by ring]
    rw [div_lt_iff₀ hlog3]
    push_cast at hlog ⊢
    simpa [Nat.cast_add, Nat.cast_one] using hlog
  linarith
end FirstPassageLinearTransport
