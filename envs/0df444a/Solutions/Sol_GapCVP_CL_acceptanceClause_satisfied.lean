-- Prove2me | solution 1 for GapCVP.CL.acceptanceClause_satisfied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/b8b69ed6-005d-49b9-ad0d-bd3548a0aba0

import Mathlib
import Definitions.Def_GapCVP

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
    (trace : Time T → Position T → Symbol S)
    (haccept : ∃ i, trace (Fin.last T) i = spec.accept) :
    satisfiesClause (assignmentOfTrace trace)
      (acceptanceClause spec.accept) := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq]
  obtain ⟨i, hi⟩ := haccept
  refine ⟨positive ((Fin.last T), i, spec.accept), ?_, ?_⟩
  · simp [acceptanceClause]
  · simp [positive, assignmentOfTrace, hi]
end GapCVP.CL
