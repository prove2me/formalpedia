-- Prove2me | solution 1 for GapCVP.CL.traceOfAssignment_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/d43b76a5-4ccd-4ba8-99a5-6e56802ac997

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_CL_traceOfAssignment_eq_of_selected

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.CL
namespace GapCVP.CL
theorem _root_.solution {T S : ℕ}
    (spec : Specification T S)
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec))
    (i : Position T) :
    traceOfAssignment spec assignment hsat 0 i = spec.input i := by
  have hsat' := hsat
  simp only [GapCVP.CL.satisfiesFormula, GapCVP.CL.satisfiesClause, decide_eq_true_eq] at hsat'
  obtain ⟨literal, hliteral, hvalue⟩ :=
    hsat' (initialClause spec.input i)
      (initialClause_mem_tableauFormula spec i)
  simp only [initialClause, Finset.mem_singleton] at hliteral
  subst literal
  apply traceOfAssignment_eq_of_selected spec assignment hsat 0 i
  simpa [positive] using hvalue
end GapCVP.CL
