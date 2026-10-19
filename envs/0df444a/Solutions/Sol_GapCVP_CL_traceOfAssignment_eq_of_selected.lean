-- Prove2me | solution 1 for GapCVP.CL.traceOfAssignment_eq_of_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/3d2577c6-36dc-4713-88d9-2aa547d36bb9

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_CL_symbol_unique_of_satisfiesFormula
import Theorems.Thm_GapCVP_CL_traceOfAssignment_selected

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
    (t : Time T) (i : Position T) (s : Symbol S)
    (hs : assignment (t, i, s) = true) :
    traceOfAssignment spec assignment hsat t i = s :=
  symbol_unique_of_satisfiesFormula spec assignment hsat t i
    (traceOfAssignment spec assignment hsat t i) s
    (traceOfAssignment_selected spec assignment hsat t i) hs
end GapCVP.CL
