-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.encodeFormulaFrom_allDistinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/e32dcc24-081e-4614-a1e1-2ba859f7f122

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_encodeClause_allDistinct

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
    (clauseIndex : ℕ) (clauses : List (Clause T S)) :
    allDistinct (encodeFormulaFrom clauseIndex clauses) := by
  induction clauses generalizing clauseIndex with
  | nil => simp [encodeFormulaFrom]
  | cons clause remaining ih =>
    rw [encodeFormulaFrom, allDistinct_append]
    exact ⟨encodeClause_allDistinct clauseIndex clause,
      ih (clauseIndex + 1)⟩
end GapCVP.ThreeCNFReduction
