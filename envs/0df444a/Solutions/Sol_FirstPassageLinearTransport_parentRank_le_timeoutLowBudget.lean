-- Prove2me | solution 1 for FirstPassageLinearTransport.parentRank_le_timeoutLowBudget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:57.94687+00:00
-- url     : https://prove2.me/submissions/b7981485-cde7-484b-bcd4-b296734f1890

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
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
theorem _root_.solution
    {K₀ : ℝ} {L m : ℕ} {rStar : ℚ}
    (hrStar : 0 < rStar)
    (hStar : (rStar : ℝ) ≤ movingLowRatio K₀ L) :
    (m : ℚ) ≤ ((timeoutTargetRank K₀ L m + 1 : ℕ) : ℚ) / rStar := by
  apply (le_div_iff₀ hrStar).2
  have hrStarR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
  have hratio0 : 0 ≤ movingLowRatio K₀ L := hrStarR.le.trans hStar
  have hfloor := Nat.lt_floor_add_one
    (movingLowRatio K₀ L * (m : ℝ))
  have hfloor' : movingLowRatio K₀ L * (m : ℝ) ≤
      (timeoutTargetRank K₀ L m + 1 : ℕ) := by
    simpa [timeoutTargetRank] using hfloor.le
  have hbound : (rStar : ℝ) * (m : ℝ) ≤
      (timeoutTargetRank K₀ L m + 1 : ℕ) :=
    (mul_le_mul_of_nonneg_right hStar (Nat.cast_nonneg m)).trans hfloor'
  have hboundQ : rStar * (m : ℚ) ≤
      ((timeoutTargetRank K₀ L m + 1 : ℕ) : ℚ) := by
    exact_mod_cast hbound
  simpa [mul_comm] using hboundQ
end FirstPassageLinearTransport
