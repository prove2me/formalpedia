-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutOddThreshold_real_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:07:18.060353+00:00
-- url     : https://prove2.me/submissions/1a372d25-de2f-4be6-8077-787f66e44f1e

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_endpoint_probability_eq_logThreeTwo
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointDisplacement_pos
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
    (timeoutOddThreshold q : ℝ) ≤ (q : ℝ) * logThreeTwo := by
  have hp : 0 < logThreeTwo := by
    rw [← endpoint_probability_eq_logThreeTwo]
    linarith [firstPassageEndpointDisplacement_pos]
  by_cases hk0 : timeoutOddThreshold q = 0
  · rw [hk0]
    simpa using mul_nonneg (Nat.cast_nonneg q) hp.le
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hnot := Nat.find_min (exists_two_pow_lt_three_pow_succ q)
      (show k < timeoutOddThreshold q by omega)
    have hpowNat : 3 ^ timeoutOddThreshold q ≤ 2 ^ q := by
      rw [hk]
      omega
    have hpow :
        (3 : ℝ) ^ timeoutOddThreshold q ≤ (2 : ℝ) ^ q := by
      exact_mod_cast hpowNat
    have hlog := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr
        (show (0 : ℝ) < (3 : ℝ) ^ timeoutOddThreshold q by positivity))
      (Set.mem_Ioi.mpr (show (0 : ℝ) < (2 : ℝ) ^ q by positivity)) hpow
    rw [Real.log_pow, Real.log_pow] at hlog
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    unfold logThreeTwo
    rw [show (q : ℝ) * (Real.log 2 / Real.log 3) =
        ((q : ℝ) * Real.log 2) / Real.log 3 by ring]
    rw [le_div_iff₀ hlog3]
    simpa using hlog
end FirstPassageLinearTransport
