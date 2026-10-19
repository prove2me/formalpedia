-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.encodeClause_allDistinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/41aee933-e5fa-45c9-a98d-9610be56ddfc

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_P2M_GapCVP_ThreeCNFReduction_accumulatorVariable_ne_paddingVariable__93525b52c478
import Theorems.Thm_P2M_GapCVP_ThreeCNFReduction_accumulatorVariable_ne_paddingVariable__c4a2f88478e9
import Theorems.Thm_GapCVP_ThreeCNFReduction_paddedUnary_allDistinct
import Theorems.Thm_GapCVP_ThreeCNFReduction_gateList_allDistinct

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
    (clauseIndex : ℕ) (clause : Clause T S) :
    allDistinct (encodeClause clauseIndex clause) := by
  rw [encodeClause, allDistinct_append, allDistinct_append]
  exact ⟨⟨paddedUnary_allDistinct _
    (accumulatorVariable_ne_paddingVariable₀ clauseIndex 0)
    (accumulatorVariable_ne_paddingVariable₁ clauseIndex 0),
    gateList_allDistinct clauseIndex 0 (sortedElements clause)⟩,
    paddedUnary_allDistinct _
      (accumulatorVariable_ne_paddingVariable₀
        clauseIndex (sortedElements clause).length)
      (accumulatorVariable_ne_paddingVariable₁
        clauseIndex (sortedElements clause).length)⟩
end GapCVP.ThreeCNFReduction
