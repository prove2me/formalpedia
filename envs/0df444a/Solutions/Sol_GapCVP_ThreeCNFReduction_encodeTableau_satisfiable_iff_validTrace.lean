-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.encodeTableau_satisfiable_iff_validTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/400bb1fa-9350-4e3a-b0fb-3fbb7e9eb9b1

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_CL_tableau_satisfiable_iff_validTrace
import Theorems.Thm_GapCVP_ThreeCNFReduction_encodeFormula_satisfiable_iff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.ThreeCNFReduction
open GapCVP.CL
namespace GapCVP.ThreeCNFReduction
theorem _root_.solution {T S : ℕ}
    (spec : Specification T S) :
    threeCNFSatisfiable (encodeTableau spec) ↔
      ∃ trace : Time T → Position T → Symbol S,
        ValidTrace spec trace := by
  exact (encodeFormula_satisfiable_iff (tableauFormula spec)).trans
    (tableau_satisfiable_iff_validTrace spec)
end GapCVP.ThreeCNFReduction
