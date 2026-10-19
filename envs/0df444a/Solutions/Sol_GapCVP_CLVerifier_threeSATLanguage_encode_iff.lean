-- Prove2me | solution 1 for GapCVP.CLVerifier.threeSATLanguage_encode_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/a314f940-2861-4276-883e-706ed46725f3

import Mathlib
import Definitions.Def_GapCVP

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.CLVerifier
open Computability GapCVP.CL
namespace GapCVP.CLVerifier
theorem _root_.solution (formula : ThreeCNF) :
    threeSATLanguage ((binaryFinEncoding ThreeCNF).encode formula) ↔
      threeCNFSatisfiable formula := by
  simp only [GapCVP.threeSATLanguage, decide_eq_true_eq]
  constructor
  · rintro ⟨candidate, hencoding, hsatisfied⟩
    have heq : candidate = formula :=
      (binaryFinEncoding ThreeCNF).encode_injective hencoding
    simpa [heq] using hsatisfied
  · intro hsatisfied
    exact ⟨formula, rfl, hsatisfied⟩
end GapCVP.CLVerifier
