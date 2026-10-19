-- Prove2me | solution 1 for GapCVP.CL.atLeastOneClause_satisfied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/1616bc17-48b2-4be9-86ae-f95336429d1f

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
    (trace : Time T → Position T → Symbol S)
    (t : Time T) (i : Position T) :
    satisfiesClause (assignmentOfTrace trace) (atLeastOneClause t i) := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq]
  refine ⟨positive (t, i, trace t i), ?_, ?_⟩
  · simp [atLeastOneClause]
  · simp [positive, assignmentOfTrace]
end GapCVP.CL
