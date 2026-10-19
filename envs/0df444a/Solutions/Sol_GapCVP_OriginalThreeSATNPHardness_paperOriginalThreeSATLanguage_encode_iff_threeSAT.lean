-- Prove2me | solution 1 for GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATLanguage_encode_iff_threeSAT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/e4a4bdcf-2032-4970-a833-9b054cbbd903

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_CLVerifier_threeSATLanguage_encode_iff
import Theorems.Thm_GapCVP_OriginalThreeSATNPHardness_paperOriginalThreeSATLanguage_encode_iff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.OriginalThreeSATNPHardness
open Computability GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.CLStructuralWholeCNFOutputTM GapCVP.CNFFiveFamilySourceIndexedORGadgetFinalCert
namespace GapCVP.OriginalThreeSATNPHardness
theorem _root_.solution
    (formula : ThreeCNF)
    (distinct : allDistinct formula) :
    paperOriginalThreeSATLanguage (encodeThreeCNF formula) ↔
      threeSATLanguage (encodeThreeCNF formula) := by
  simp only [GapCVP.ThreeCNFReduction.allDistinct, decide_eq_true_eq] at distinct
  rw [paperOriginalThreeSATLanguage_encode_iff]
  change
    (∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) ↔
      threeSATLanguage ((binaryFinEncoding ThreeCNF).encode formula)
  rw [GapCVP.CLVerifier.threeSATLanguage_encode_iff]
  simp only [GapCVP.threeCNFSatisfiable, decide_eq_true_eq]
  exact ⟨fun satisfaction => ⟨distinct, satisfaction⟩,
    fun satisfaction => satisfaction.2⟩
end GapCVP.OriginalThreeSATNPHardness
