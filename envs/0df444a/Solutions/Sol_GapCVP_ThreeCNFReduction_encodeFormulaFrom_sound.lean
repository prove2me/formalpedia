-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.encodeFormulaFrom_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/60e4d957-dc87-4c7e-8cf4-2ba795f5059c

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_encodeClause_sound

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
    (assignment : ℕ → Bool)
    (clauseIndex : ℕ) (clauses : List (Clause T S))
    (hsatisfied : satisfies assignment
      (encodeFormulaFrom clauseIndex clauses)) :
    ∀ clause ∈ clauses,
      CL.satisfiesClause (restrictAssignment assignment) clause := by
  induction clauses generalizing clauseIndex with
  | nil => simp
  | cons clause remaining ih =>
    simp only [encodeFormulaFrom, satisfies_append] at hsatisfied
    obtain ⟨hclause, hremaining⟩ := hsatisfied
    intro candidate hcandidate
    simp only [List.mem_cons] at hcandidate
    rcases hcandidate with rfl | hcandidate
    · exact encodeClause_sound assignment clauseIndex _ hclause
    · exact ih (clauseIndex + 1) hremaining candidate hcandidate
end GapCVP.ThreeCNFReduction
