-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingFirstBadSourcesAtRank_subset_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:40.992834+00:00
-- url     : https://prove2.me/submissions/449514fc-1953-4beb-ba59-be66c511b8db

import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_scaledReverseLoss_le
import Theorems.Thm_FirstPassageLinearTransport_MixedRecertificationRun_toCertifiedRankChain
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_toCertifiedRankChain
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_elapsed_le_horizon
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_toMixed
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
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
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
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


attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFirstBadSourcesAtRank

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData) {M S q : ℕ} :
    shrinkingFirstBadSourcesAtRank P M S q ⊆
      lossFilteredTransportedSourcesAtTimes M (2 ^ q)
        (shrinkingFeasibleTimes P M S q)
        (landingBad q (shrinkingTargetTolerance P M S q))
        (((q + 2 : ℕ) : ℚ) / P.rStar) := by
  classical
  intro n hn
  rcases mem_shrinkingFirstBadSourcesAtRank.mp hn with
    ⟨hnShell, h, hrun, hbad⟩
  apply mem_lossFilteredTransportedSourcesAtTimes.mpr
  refine ⟨hnShell, h, ?_, hrun.directFirstPassage, hbad, ?_⟩
  · apply mem_shrinkingFeasibleTimes.mpr
    exact ⟨hrun.elapsed_le_horizon, n, hnShell, hrun⟩
  · exact (hrun.toMixed.toCertifiedRankChain P.rStar_pos).scaledReverseLoss_le
      P.rStar_pos
end FirstPassageLinearTransport
