-- Prove2me | solution 1 for GapCVP.CLStructuralWholeCNFOutputTM.structuralWholeThreeCNF_allDistinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/cfd003d7-6d4e-4baa-bdf5-c11925504789

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_encodeFormula_allDistinct
import Theorems.Thm_GapCVP_CLStructuralWholeCNFOutputTM_structuralWholeThreeCNF_eq_encodeTableau

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.CLStructuralWholeCNFOutputTM
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLCellRowBounds GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
namespace GapCVP.CLStructuralWholeCNFOutputTM
theorem _root_.solution
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    allDistinct (structuralWholeThreeCNF bound machine x) := by
  rw [structuralWholeThreeCNF_eq_encodeTableau]
  exact encodeFormula_allDistinct
    (tableauFormula
      (paddedAcceptancePhaseSpecification bound machine x))
end GapCVP.CLStructuralWholeCNFOutputTM
