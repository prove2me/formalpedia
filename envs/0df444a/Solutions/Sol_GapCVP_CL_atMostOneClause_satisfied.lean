-- Prove2me | solution 1 for GapCVP.CL.atMostOneClause_satisfied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/d7e6f1a9-15eb-4c16-80ed-8d82c837effa

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
    (t : Time T) (i : Position T) (a b : Symbol S)
    (hab : a < b) :
    satisfiesClause (assignmentOfTrace trace) (atMostOneClause t i a b) := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq]
  by_cases ha : trace t i = a
  · refine ⟨negative (t, i, b), by simp [atMostOneClause], ?_⟩
    simp [negative, assignmentOfTrace, ha, ne_of_lt hab]
  · refine ⟨negative (t, i, a), by simp [atMostOneClause], ?_⟩
    simp [negative, assignmentOfTrace, ha]
end GapCVP.CL
