-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.encodeFormulaFrom_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/f346a175-9d72-4cac-b8fb-c3365dcfa9c2

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_drop_succ_of_drop_cons
import Theorems.Thm_GapCVP_ThreeCNFReduction_encodeClause_complete

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.ThreeCNFReduction
open GapCVP.CL
namespace GapCVP.ThreeCNFReduction
theorem _root_.solution {T S : ℕ}
    (clauses : List (Clause T S))
    (assignment : Variable T S → Bool)
    (clauseIndex : ℕ) (remaining : List (Clause T S))
    (hdrop : clauses.drop clauseIndex = remaining)
    (hsatisfied : ∀ clause ∈ clauses,
      CL.satisfiesClause assignment clause) :
    satisfies (liftAssignment clauses assignment)
      (encodeFormulaFrom clauseIndex remaining) := by
  induction remaining generalizing clauseIndex with
  | nil => simp [encodeFormulaFrom]
  | cons clause tail ih =>
    have hlookup : clauses[clauseIndex]? = some clause := by
      have hhead := congrArg List.head? hdrop
      simpa [List.head?_drop] using hhead
    have hmem : clause ∈ clauses := by
      obtain ⟨hbound, hget⟩ :=
        List.getElem?_eq_some_iff.mp hlookup
      exact hget ▸ List.getElem_mem hbound
    have htail := drop_succ_of_drop_cons
      clauses clauseIndex clause tail hdrop
    rw [encodeFormulaFrom, satisfies_append]
    exact ⟨encodeClause_complete clauses assignment clauseIndex clause
      hlookup (hsatisfied clause hmem),
      ih (clauseIndex + 1) htail⟩
end GapCVP.ThreeCNFReduction
