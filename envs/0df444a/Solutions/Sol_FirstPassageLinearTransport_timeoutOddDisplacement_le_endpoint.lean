-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutOddDisplacement_le_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:18.604963+00:00
-- url     : https://prove2.me/submissions/798c1c58-757c-4c82-ad1b-349450eb56c9

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_timeoutOddThreshold_real_upper
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
theorem _root_.solution
    {K₀ : ℝ} {L m : ℕ}
    (hr0 : 0 ≤ movingLowRatio K₀ L)
    (hr1 : movingLowRatio K₀ L ≤ 1)
    (hm : 0 < m) :
    timeoutOddDisplacement K₀ L m ≤
      firstPassageEndpointDisplacement := by
  let r := movingLowRatio K₀ L
  let q := timeoutTargetRank K₀ L m
  let k := timeoutOddThreshold q
  have hmR : 0 < (m : ℝ) := by positivity
  have hp : 0 < logThreeTwo := by
    rw [← endpoint_probability_eq_logThreeTwo]
    linarith [firstPassageEndpointDisplacement_pos]
  have hq : (q : ℝ) ≤ r * (m : ℝ) := by
    dsimp [q, r]
    simpa [timeoutTargetRank] using
      (Nat.floor_le (mul_nonneg hr0 (Nat.cast_nonneg m)))
  have hk : (k : ℝ) ≤ (q : ℝ) * logThreeTwo := by
    simpa [k] using timeoutOddThreshold_real_upper q
  have hkm : (k : ℝ) / (m : ℝ) ≤ logThreeTwo := by
    have hqr : (q : ℝ) * logThreeTwo ≤
        r * (m : ℝ) * logThreeTwo :=
      mul_le_mul_of_nonneg_right hq hp.le
    have hrm : r * (m : ℝ) * logThreeTwo ≤
        (m : ℝ) * logThreeTwo := by
      have hr1' : r ≤ 1 := by simpa [r] using hr1
      have hbase : r * (m : ℝ) ≤ (m : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right hr1' (Nat.cast_nonneg m)
      exact mul_le_mul_of_nonneg_right hbase hp.le
    rw [div_le_iff₀ hmR]
    nlinarith [hk, hqr, hrm]
  have hendpoint :
      firstPassageEndpointDisplacement = logThreeTwo - 1 / 2 := by
    linarith [endpoint_probability_eq_logThreeTwo]
  rw [timeoutOddDisplacement, hendpoint]
  exact sub_le_sub_right hkm _
end FirstPassageLinearTransport
