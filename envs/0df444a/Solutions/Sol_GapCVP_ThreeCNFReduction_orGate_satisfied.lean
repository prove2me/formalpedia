-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.orGate_satisfied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/b17f476f-2ab1-448c-b31f-4ef9bddfd241

import Mathlib
import Definitions.Def_GapCVP

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.ThreeCNFReduction
open GapCVP.CL
namespace GapCVP.ThreeCNFReduction
theorem _root_.solution (assignment : ℕ → Bool)
    (a b output : Literal) :
    satisfies assignment (orGate a b output) ↔
      (literalSatisfied assignment output ↔
        literalSatisfied assignment a ∨ literalSatisfied assignment b) := by
  simp only [orGate, satisfies_append, paddedBinary_satisfied,
    satisfies_singleton, clauseSatisfied_triple, literalSatisfied_negate]
  tauto
end GapCVP.ThreeCNFReduction
