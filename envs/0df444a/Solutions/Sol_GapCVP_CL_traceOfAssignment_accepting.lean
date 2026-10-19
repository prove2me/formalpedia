-- Prove2me | solution 1 for GapCVP.CL.traceOfAssignment_accepting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/fb5979b8-8a81-4453-ad1d-dac9e351c2d7

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
    (hsat : satisfiesFormula assignment (tableauFormula spec)) :
    ∃ i : Position T,
      traceOfAssignment spec assignment hsat (Fin.last T) i = spec.accept := by
  have hsat' := hsat
  simp only [GapCVP.CL.satisfiesFormula, GapCVP.CL.satisfiesClause, decide_eq_true_eq] at hsat'
  obtain ⟨literal, hliteral, hvalue⟩ :=
    hsat' (acceptanceClause spec.accept)
      (acceptanceClause_mem_tableauFormula spec)
  simp only [acceptanceClause, Finset.mem_image,
    Finset.mem_univ, true_and] at hliteral
  obtain ⟨i, rfl⟩ := hliteral
  refine ⟨i, traceOfAssignment_eq_of_selected spec assignment hsat
    (Fin.last T) i spec.accept ?_⟩
  simpa [positive] using hvalue
end GapCVP.CL
