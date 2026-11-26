-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.currentRank_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:40.17731+00:00
-- url     : https://prove2.me/submissions/ff6a3f18-9ba7-4af5-bac0-08b257fe90a2

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_currentRank_high_or_low
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
noncomputable section
namespace FirstPassageLinearTransport
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q Q : ℕ}
    (hHigh : (Q : ℝ) ≤ (P.rHi : ℝ) * (S : ℝ))
    (hLowRatio : (1 / 2 : ℝ) ≤ movingLowRatio K₀ L)
    (hQL : 2 * Q ≤ L)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    Q ≤ q := by
  rcases hrun.currentRank_high_or_low with hhigh | hlow
  · rcases hhigh with ⟨m, hSm, rfl⟩
    apply Nat.le_floor
    have hr0 : (0 : ℝ) ≤ (P.rHi : ℝ) := P.pHi.r_pos.le
    have hSmR : (S : ℝ) ≤ (m : ℝ) := by exact_mod_cast hSm
    exact hHigh.trans (mul_le_mul_of_nonneg_left hSmR hr0)
  · rcases hlow with ⟨m, hLm, rfl⟩
    have hQ : (Q : ℝ) ≤ (1 / 2 : ℝ) * (L : ℝ) := by
      have hQLR : (2 : ℝ) * (Q : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast hQL
      linarith
    have hLmR : (L : ℝ) ≤ (m : ℝ) := by exact_mod_cast hLm
    have hratio0 : 0 ≤ movingLowRatio K₀ L := by linarith
    have htarget : (Q : ℝ) ≤ movingLowRatio K₀ L * (m : ℝ) := by
      calc
        (Q : ℝ) ≤ (1 / 2 : ℝ) * (L : ℝ) := hQ
        _ ≤ movingLowRatio K₀ L * (L : ℝ) := by
          exact mul_le_mul_of_nonneg_right hLowRatio (Nat.cast_nonneg L)
        _ ≤ movingLowRatio K₀ L * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hLmR hratio0
    simpa [timeoutTargetRank] using (Nat.le_floor htarget)
end TimeoutRecertificationRun
end FirstPassageLinearTransport
