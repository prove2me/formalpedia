-- Prove2me | solution 1 for GapCVP.CLStructuralWholeCNFOutputTM.structuralWholeCNFWord_mem_threeSAT_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/bb53cf58-5602-4f15-8b16-ceef3b1ff615

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_CLNondeterminism_compiledTableau_iff_verifier
import Theorems.Thm_GapCVP_CLStructuralWholeCNFOutputTM_structuralWholeCNFWord_eq_encodedTableau

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
    threeSATLanguage (structuralWholeCNFWord bound machine x) ↔
      ∃ certificate : List Bool,
        certificate.length ≤ bound.eval x.length ∧
          verifier (x, certificate) = true := by
  rw [structuralWholeCNFWord_eq_encodedTableau]
  exact compiledTableau_iff_verifier bound machine
    (paddedAcceptanceLocalTableauCompiler bound machine) x
end GapCVP.CLStructuralWholeCNFOutputTM
