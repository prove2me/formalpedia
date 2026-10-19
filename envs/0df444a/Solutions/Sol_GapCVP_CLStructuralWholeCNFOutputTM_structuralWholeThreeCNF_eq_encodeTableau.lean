-- Prove2me | solution 1 for GapCVP.CLStructuralWholeCNFOutputTM.structuralWholeThreeCNF_eq_encodeTableau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/dd7cc016-e26c-42c3-97f1-e68219faa857

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
    structuralWholeThreeCNF bound machine x =
      ThreeCNFReduction.encodeTableau
        (paddedAcceptancePhaseSpecification bound machine x) := by
  rfl
end GapCVP.CLStructuralWholeCNFOutputTM
