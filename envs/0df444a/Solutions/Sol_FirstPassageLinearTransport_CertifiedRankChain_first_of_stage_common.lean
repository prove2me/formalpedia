-- Prove2me | solution 1 for FirstPassageLinearTransport.CertifiedRankChain.first_of_stage_common
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:25.056305+00:00
-- url     : https://prove2.me/submissions/ee4f7394-37fd-49f7-ac05-3762dd41f39b

import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
import Theorems.Thm_FirstPassageLinearTransport_parentRank_le_commonTargetBudget
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageLength_isFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_stageLength_le_shell
import Theorems.Thm_FirstPassageLinearTransport_targetScale_rat
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace CertifiedRankChain
theorem _root_.solution
    {rStar r : ℚ} {eta : ℝ} (p : StageSetup (r : ℝ) eta)
    (hrStar : 0 < rStar) (hStar : rStar ≤ r) {m n : ℕ}
    (hm0 : p.M0 ≤ m) (hnShell : n ∈ dyadicShell m)
    (hnGood : n ∈ initialWindowGood eta) :
    CertifiedRankChain rStar n (stageLength p n) (rationalTargetRank r m) := by
  apply CertifiedRankChain.first
  · simpa [targetScale_rat] using
      stageLength_isFirstPassage p hm0 hnShell hnGood
  · exact stageLength_le_shell p hm0 hnShell hnGood
  · exact parentRank_le_commonTargetBudget hrStar hStar m
end CertifiedRankChain
end FirstPassageLinearTransport
