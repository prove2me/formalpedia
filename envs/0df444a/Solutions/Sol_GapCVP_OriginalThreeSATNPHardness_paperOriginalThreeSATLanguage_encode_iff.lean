-- Prove2me | solution 1 for GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATLanguage_encode_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/02f57e9e-75a3-4fd1-b745-98c69d10c42c

import Mathlib
import Definitions.Def_GapCVP

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
theorem _root_.solution (formula : ThreeCNF) :
    paperOriginalThreeSATLanguage (encodeThreeCNF formula) ↔
      ∃ assignment : ℕ → Bool,
        ∀ clause ∈ formula, clauseSatisfied assignment clause := by
  rw [paperOriginalThreeSATLanguage_iff]
  constructor
  · rintro ⟨candidate, encoding, assignment, satisfied⟩
    have sameEncoding := congrArg decodeThreeCNF encoding
    have sameFormula : candidate = formula := by
      simpa only [decodeThreeCNF_encode, Option.some.injEq]
        using sameEncoding
    subst candidate
    exact ⟨assignment, satisfied⟩
  · rintro ⟨assignment, satisfied⟩
    exact ⟨formula, rfl, assignment, satisfied⟩
end GapCVP.OriginalThreeSATNPHardness
