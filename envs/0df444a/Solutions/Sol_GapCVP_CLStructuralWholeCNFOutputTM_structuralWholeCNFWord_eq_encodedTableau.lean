-- Prove2me | solution 1 for GapCVP.CLStructuralWholeCNFOutputTM.structuralWholeCNFWord_eq_encodedTableau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/aee7660e-ae64-468f-832b-9ed0f72e04d7

import Mathlib
import Definitions.Def_GapCVP

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
    structuralWholeCNFWord bound machine x =
      encodedTableau (paddedStructuralTableauSimulation
        bound machine) x := by
  rfl
end GapCVP.CLStructuralWholeCNFOutputTM
