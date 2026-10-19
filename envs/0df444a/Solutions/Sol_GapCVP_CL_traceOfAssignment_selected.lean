-- Prove2me | solution 1 for GapCVP.CL.traceOfAssignment_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/0df21ef2-ee36-4218-8432-b2bf03ccdc52

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
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec))
    (t : Time T) (i : Position T) :
    assignment (t, i, traceOfAssignment spec assignment hsat t i) = true :=
  Classical.choose_spec
    (symbol_exists_of_satisfiesFormula spec assignment hsat t i)
end GapCVP.CL
