-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutTimePotential_low_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:46.685499+00:00
-- url     : https://prove2.me/submissions/9368a186-36f5-4072-a2e5-404a3bc15127

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_lowTimeout_duration_error_le
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
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
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
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
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



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) {K₀ : ℝ} {L M S qPrev m x : ℕ}
    (hmS : m < S) (hpass : LowTimeoutPassage K₀ L m x)
    (hmPrevLo : m ≤ qPrev) (hmPrevHi : qPrev ≤ m + 1)
    (hqparent : timeoutTargetRank K₀ L m < m) :
    (|driftGap * (hpass.duration : ℝ) -
        ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1) +
        timeoutTimePotential P M S (timeoutTargetRank K₀ L m) ≤
      timeoutTimePotential P M S qPrev := by
  have hlocal := lowTimeout_duration_error_le hmS hpass hqparent
  have hqLow : ¬S < timeoutTargetRank K₀ L m := by omega
  have hprevLow : ¬S < qPrev := by omega
  simp only [timeoutTimePotential, if_neg hqLow, if_neg hprevLow]
  have hqR : (timeoutTargetRank K₀ L m : ℝ) + 1 ≤ m := by
    exact_mod_cast hqparent
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hmul : (S : ℝ) *
      ((timeoutTargetRank K₀ L m : ℝ) + 1) ≤ (S : ℝ) * (m : ℝ) :=
    mul_le_mul_of_nonneg_left hqR hS0
  have hmPrevR : (m : ℝ) ≤ (qPrev : ℝ) := by exact_mod_cast hmPrevLo
  calc
    (|driftGap * (hpass.duration : ℝ) -
          ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1) +
        (S : ℝ) * (timeoutTargetRank K₀ L m : ℝ) ≤
      (S : ℝ) + (S : ℝ) * (timeoutTargetRank K₀ L m : ℝ) :=
        add_le_add hlocal (le_refl _)
    _ = (S : ℝ) * ((timeoutTargetRank K₀ L m : ℝ) + 1) := by ring
    _ ≤ (S : ℝ) * (m : ℝ) := hmul
    _ ≤ (S : ℝ) * (qPrev : ℝ) :=
      mul_le_mul_of_nonneg_left hmPrevR hS0
end FirstPassageLinearTransport
