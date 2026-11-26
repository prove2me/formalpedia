-- Prove2me | solution 1 for FirstPassageLinearTransport.generatedFirstBadSources_subset_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:10.487816+00:00
-- url     : https://prove2.me/submissions/b2a18bdb-c177-472b-a7a1-5a3eca4fb1d0

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_scaledReverseLoss_le
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
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
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
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


attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M L U H : ℕ} {r : ℚ} {t : ℝ} (hr : 0 < r) :
    generatedFirstBadSources M L U H r t ⊆
      firstBadLandingEnvelope M L U H r t := by
  intro n hn
  have hmem := mem_generatedFirstBadSources.mp hn
  rcases hmem.2 with ⟨h, q, hLq, hqU, hh1, hhH, hchain, hbad⟩
  have hfp := hchain.directFirstPassage
  have hloss := hchain.scaledReverseLoss_le hr
  exact mem_firstBadLandingEnvelope.mpr
    ⟨q, hLq, hqU, hmem.1, h, hh1, hhH, hfp, hbad, hloss⟩
end FirstPassageLinearTransport
