-- Prove2me | solution 1 for FirstPassageLinearTransport.abs_shortcutLogDeviation_highStage_le_durationError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:25:23.621928+00:00
-- url     : https://prove2.me/submissions/c51d040b-4359-481d-aff9-41b8b4e95173

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_abs_shortcutLogDeviation_le_of_initialWindowGood
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_log_two_eq_of_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutHighFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageLength_le_shell
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_timeoutFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_timeoutHighFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons


attribute [local simp] FirstPassageLinearTransport.shortcutFirstPassageTime_self
attribute [local simp] FirstPassageLinearTransport.rawFirstPassageTime_self

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) {M m x j : ℕ}
    (hm0 : P.pHi.M0 ≤ m)
    (hxShell : x ∈ dyadicShell m)
    (hxGood : x ∈ initialWindowGood (timeoutHighTolerance P M m))
    (hj : j ≤ stageLength (timeoutHighSetup P M m) x) :
    |shortcutLogDeviation x j| ≤
      timeoutDurationError (timeoutHighTolerance P M m) m := by
  have hx : 0 < x := by
    have hxLower := (mem_dyadicShell.mp hxShell).1
    have hpow : 0 < 2 ^ m := by positivity
    omega
  have hjm := hj.trans
    (stageLength_le_shell (timeoutHighSetup P M m) hm0 hxShell hxGood)
  have hjlog : j ≤ Nat.log 2 x := by
    simpa [log_two_eq_of_mem_dyadicShell hxShell] using hjm
  have hlocal := abs_shortcutLogDeviation_le_of_initialWindowGood
    hx hxGood hjlog
  have hxUpperNat := (mem_dyadicShell.mp hxShell).2
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hxUpperR : (x : ℝ) < ((2 ^ (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast hxUpperNat
  have hlogUpper := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr hxR)
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < ((2 ^ (m + 1) : ℕ) : ℝ)))
    hxUpperR
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hlogUpper
  rw [Real.log_pow] at hlogUpper
  have ht0 := (timeoutHighTolerance_pos P M m).le
  have hlogTwo0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwo1 : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hm0R : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have htlog := mul_le_mul_of_nonneg_left hlogUpper.le ht0
  have hprod0 : 0 ≤ timeoutHighTolerance P M m * ((m : ℝ) + 1) :=
    mul_nonneg ht0 (by linarith)
  have hscaled :
      timeoutHighTolerance P M m * (((m : ℝ) + 1) * Real.log 2) ≤
        timeoutHighTolerance P M m * ((m : ℝ) + 1) := by
    calc
      _ = (timeoutHighTolerance P M m * ((m : ℝ) + 1)) * Real.log 2 := by ring
      _ ≤ (timeoutHighTolerance P M m * ((m : ℝ) + 1)) * 1 :=
        mul_le_mul_of_nonneg_left hlogTwo1.le hprod0
      _ = _ := by ring
  rw [timeoutDurationError]
  push_cast at hlogUpper htlog
  nlinarith
end FirstPassageLinearTransport
