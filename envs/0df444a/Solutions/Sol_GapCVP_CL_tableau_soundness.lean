-- Prove2me | solution 1 for GapCVP.CL.tableau_soundness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/f58b2fb3-7e5a-4a23-a06e-ae077aa9c0e1

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_CL_traceOfAssignment_initial
import Theorems.Thm_GapCVP_CL_traceOfAssignment_accepting
import Theorems.Thm_GapCVP_CL_traceOfAssignment_transition

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
    ValidTrace spec (traceOfAssignment spec assignment hsat) := by
  simp only [GapCVP.CL.ValidTrace, decide_eq_true_eq]
  exact ⟨traceOfAssignment_initial spec assignment hsat,
    traceOfAssignment_accepting spec assignment hsat,
    traceOfAssignment_transition spec assignment hsat⟩
end GapCVP.CL
