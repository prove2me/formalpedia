-- Prove2me | solution 1 for GapCVP.CL.tableau_satisfiable_iff_validTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/c535baaf-8615-40e0-b12d-bcfb84411c06

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_CL_tableau_completeness
import Theorems.Thm_GapCVP_CL_tableau_soundness

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.CL
namespace GapCVP.CL
theorem _root_.solution {T S : ℕ}
    (spec : Specification T S) :
    (∃ assignment : Variable T S → Bool,
      satisfiesFormula assignment (tableauFormula spec)) ↔
      ∃ trace : Time T → Position T → Symbol S, ValidTrace spec trace := by
  constructor
  · rintro ⟨assignment, hs⟩
    exact ⟨traceOfAssignment spec assignment hs,
      tableau_soundness spec assignment hs⟩
  · rintro ⟨trace, ht⟩
    exact ⟨assignmentOfTrace trace, tableau_completeness spec trace ht⟩
end GapCVP.CL
