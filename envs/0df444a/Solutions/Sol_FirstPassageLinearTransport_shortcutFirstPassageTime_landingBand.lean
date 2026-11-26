-- Prove2me | solution 1 for FirstPassageLinearTransport.shortcutFirstPassageTime_landingBand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:51:01.388111+00:00
-- url     : https://prove2.me/submissions/055e81d5-4a81-43cb-aa95-4dc90427bef1

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_mem
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_le
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
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
import Theorems.Thm_FirstPassageLinearTransport_orbit_succ
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
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
    {n k : ℕ} {z : ℝ}
    (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z) :
    z < 2 * (orbit (shortcutFirstPassageTime n z) n : ℝ) ∧
      (orbit (shortcutFirstPassageTime n z) n : ℝ) ≤ z := by
  let tau := shortcutFirstPassageTime n z
  have htauMem := shortcutFirstPassageTime_mem hk
  change (orbit tau n : ℝ) ≤ z at htauMem
  have htauPos : 0 < tau := by
    by_contra hzero
    have htau0 : tau = 0 := Nat.eq_zero_of_not_pos hzero
    rw [htau0, orbit_zero] at htauMem
    exact (not_le_of_gt hzStart) htauMem
  let prev := tau - 1
  have htauEq : tau = prev + 1 := by
    dsimp [prev]
    omega
  have hprevAbove : z < (orbit prev n : ℝ) := by
    by_contra hnot
    have hprevMem : (orbit prev n : ℝ) ≤ z := le_of_not_gt hnot
    have htauLe0 : shortcutFirstPassageTime n z ≤ prev :=
      shortcutFirstPassageTime_le hprevMem
    have htauLe : tau ≤ prev := by simpa [tau] using htauLe0
    omega
  have hstepNat : orbit prev n ≤ 2 * orbit tau n := by
    rw [htauEq, orbit_succ]
    rcases Nat.mod_two_eq_zero_or_one (orbit prev n) with heven | hodd
    · rw [two_mul_shortcut_of_even heven]
    · rw [two_mul_shortcut_of_odd hodd]
      omega
  have hstep : (orbit prev n : ℝ) ≤
      2 * (orbit tau n : ℝ) := by exact_mod_cast hstepNat
  exact ⟨hprevAbove.trans_le hstep, htauMem⟩
end FirstPassageLinearTransport
