-- Prove2me | solution 1 for FirstPassageLinearTransport.simultaneousFirstPassageTime_centered_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:49.923854+00:00
-- url     : https://prove2.me/submissions/05dee197-a73a-49ef-b1d7-f86aba3cd0e5

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_eq_rawTime_shortcutFirstPassageTime
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_centered_profile
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_centered_profile
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_fixedPolylogClockCritical_pos
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
    {n k ell : ℕ} {z Eshort Eraw : ℝ}
    (hn : 0 < n)
    (hzLanding : (orbit k n : ℝ) ≤ z)
    (hzSource : z ≤ (n : ℝ))
    (hell : ell = rawTime n k)
    (hshortcut : ∀ j : ℕ, j ≤ k →
      |shortcutLogDeviation n j| ≤ Eshort)
    (hraw : ∀ i : ℕ, i ≤ ell →
      |rawLogDeviation n i| ≤ Eraw) :
    |(shortcutFirstPassageTime n z : ℝ) -
        fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
      |(rawFirstPassageTime n z : ℝ) -
        (3 / 2) * fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| ≤
        fixedPolylogClockCritical * (Eshort + Real.log 2) +
          (3 / 2) * fixedPolylogClockCritical * (Eraw + Real.log 2) ∧
      rawOrbit (rawFirstPassageTime n z) n =
        orbit (shortcutFirstPassageTime n z) n := by
  rcases hzSource.lt_or_eq with hzStart | hzEq
  · have hshort := shortcutFirstPassageTime_centered_profile
      hn hzStart hzLanding hshortcut
    have hrawTube : ∀ i : ℕ, i ≤ rawTime n k →
        |rawLogDeviation n i| ≤ Eraw := by
      intro i hi
      exact hraw i (by simpa [hell] using hi)
    have hrawProfile := rawFirstPassageTime_centered_profile
      hn hzStart hzLanding hrawTube
    have hid := rawFirstPassageTime_eq_rawTime_shortcutFirstPassageTime
      hn hzStart hzLanding
    exact ⟨add_le_add hshort hrawProfile, hid.2⟩
  · subst z
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hshort0 := shortcutFirstPassageTime_self (n := n)
    have hraw0 := rawFirstPassageTime_self (n := n)
    have hlog0 : Real.log ((n : ℝ) / (n : ℝ)) = 0 := by
      rw [div_self hnR, Real.log_one]
    constructor
    · rw [hshort0, hraw0, hlog0]
      norm_num
      have hlogTwo0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
      have hc0 : 0 ≤ fixedPolylogClockCritical :=
        fixedPolylogClockCritical_pos.le
      have hEshort0 : 0 ≤ Eshort := by
        have hzero := hshortcut 0 (Nat.zero_le k)
        simpa [shortcutLogDeviation] using (abs_nonneg (shortcutLogDeviation n 0)).trans hzero
      have hEraw0 : 0 ≤ Eraw := by
        have hzero := hraw 0 (Nat.zero_le ell)
        exact (abs_nonneg (rawLogDeviation n 0)).trans hzero
      positivity
    · simp [hshort0, hraw0, rawOrbit_zero]
end FirstPassageLinearTransport
