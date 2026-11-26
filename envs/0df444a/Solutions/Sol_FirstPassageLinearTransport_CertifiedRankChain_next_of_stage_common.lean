-- Prove2me | solution 1 for FirstPassageLinearTransport.CertifiedRankChain.next_of_stage_common
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:31.804971+00:00
-- url     : https://prove2.me/submissions/c451e3b3-2b1a-45d6-bac0-6eebd6f4d601

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
    (hrStar : 0 < rStar) (hStar : rStar ≤ r)
    {n elapsed qprev m : ℕ}
    (hchain : CertifiedRankChain rStar n elapsed qprev)
    (hm0 : p.M0 ≤ m) (hsourceShell : orbit elapsed n ∈ dyadicShell m)
    (hsourceGood : orbit elapsed n ∈ initialWindowGood eta)
    (hgap : rationalTargetRank r m < qprev) :
    CertifiedRankChain rStar n
      (elapsed + stageLength p (orbit elapsed n))
      (rationalTargetRank r m) := by
  apply CertifiedRankChain.next hchain hgap
  · simpa [targetScale_rat] using
      stageLength_isFirstPassage p hm0 hsourceShell hsourceGood
  · exact stageLength_le_shell p hm0 hsourceShell hsourceGood
  · exact parentRank_le_commonTargetBudget hrStar hStar m
end CertifiedRankChain
end FirstPassageLinearTransport
