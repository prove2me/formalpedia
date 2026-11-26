-- Prove2me | solution 1 for FirstPassageLinearTransport.CertifiedRankChain.first_of_stage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:38.825243+00:00
-- url     : https://prove2.me/submissions/5c9362fb-171a-49c8-a951-18940afe96ff

import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
import Theorems.Thm_FirstPassageLinearTransport_targetScale_rat
import Theorems.Thm_FirstPassageLinearTransport_parentRank_le_rationalTargetBudget
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
    {r : ℚ} {eta : ℝ} (p : StageSetup (r : ℝ) eta)
    (hr : 0 < r) {m n : ℕ}
    (hm0 : p.M0 ≤ m) (hnShell : n ∈ dyadicShell m)
    (hnGood : n ∈ initialWindowGood eta) :
    CertifiedRankChain r n (stageLength p n) (rationalTargetRank r m) := by
  apply CertifiedRankChain.first
  · simpa [targetScale_rat] using
      stageLength_isFirstPassage p hm0 hnShell hnGood
  · exact stageLength_le_shell p hm0 hnShell hnGood
  · exact parentRank_le_rationalTargetBudget hr m
end CertifiedRankChain
end FirstPassageLinearTransport
