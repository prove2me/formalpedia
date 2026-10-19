-- Prove2me | solution 1 for GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATIsNPHard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/170e0de8-dcbc-4a50-8ab3-bcd23f715cab

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_OriginalThreeSATNPHardness_structuralWholeCNFWord_mem_paperOriginalThreeSAT_iff

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
theorem _root_.solution :
    NPHard paperOriginalThreeSATLanguage := by
  simp only [GapCVP.NPHard, decide_eq_true_eq]
  intro language membership
  simp only [GapCVP.IsNP, decide_eq_true_eq] at membership
  obtain ⟨bound, verifier, ⟨machine⟩, correctness⟩ := membership
  refine ⟨{
    map := structuralWholeCNFWord bound machine
    polynomial_time :=
      ⟨actualWholeStructuralCNFOutputComputable bound machine⟩
    correct := ?_
  }⟩
  intro input
  exact (correctness input).trans
    (structuralWholeCNFWord_mem_paperOriginalThreeSAT_iff
      bound machine input).symm
end GapCVP.OriginalThreeSATNPHardness
