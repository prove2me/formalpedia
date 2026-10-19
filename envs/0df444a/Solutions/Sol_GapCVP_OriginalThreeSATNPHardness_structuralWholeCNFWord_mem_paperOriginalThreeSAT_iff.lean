-- Prove2me | solution 1 for GapCVP.OriginalThreeSATNPHardness.structuralWholeCNFWord_mem_paperOriginalThreeSAT_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/152d23e2-9292-4be5-9cf5-3e49722e3a55

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_CLStructuralWholeCNFOutputTM_structuralWholeCNFWord_mem_threeSAT_iff
import Theorems.Thm_GapCVP_CLStructuralWholeCNFOutputTM_structuralWholeThreeCNF_allDistinct
import Theorems.Thm_GapCVP_OriginalThreeSATNPHardness_paperOriginalThreeSATLanguage_encode_iff_threeSAT

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
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) :
    paperOriginalThreeSATLanguage
        (structuralWholeCNFWord bound machine input) ↔
      ∃ certificate : List Bool,
        certificate.length ≤ bound.eval input.length ∧
          verifier (input, certificate) = true := by
  exact
    (paperOriginalThreeSATLanguage_encode_iff_threeSAT
      (structuralWholeThreeCNF bound machine input)
      (structuralWholeThreeCNF_allDistinct bound machine input)).trans
        (structuralWholeCNFWord_mem_threeSAT_iff bound machine input)
end GapCVP.OriginalThreeSATNPHardness
