-- Prove2me | solution 1 for GapCVP.CL.initialClause_satisfied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/78e11e8e-793f-4f9b-a1b7-5a22302a5581

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
    (hinit : ∀ i, trace 0 i = spec.input i) (i : Position T) :
    satisfiesClause (assignmentOfTrace trace) (initialClause spec.input i) := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq]
  refine ⟨positive ((0 : Time T), i, spec.input i), by simp [initialClause], ?_⟩
  simp [positive, assignmentOfTrace, hinit i]
end GapCVP.CL
