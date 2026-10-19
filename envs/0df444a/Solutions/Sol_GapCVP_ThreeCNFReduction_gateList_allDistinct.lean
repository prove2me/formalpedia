-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.gateList_allDistinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/aa4fce5e-5cf0-465c-bffe-f69138c55cc5

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_sourceVariable_ne_accumulatorVariable
import Theorems.Thm_P2M_GapCVP_ThreeCNFReduction_sourceVariable_ne_paddingVariable__063b26f09f58
import Theorems.Thm_P2M_GapCVP_ThreeCNFReduction_accumulatorVariable_ne_paddingVariable__93525b52c478
import Theorems.Thm_GapCVP_ThreeCNFReduction_consecutive_accumulatorVariables_ne
import Theorems.Thm_GapCVP_ThreeCNFReduction_orGate_allDistinct

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
    (clauseIndex prefixIndex : ℕ)
    (literals : List (SignedLiteral T S)) :
    allDistinct (gateList clauseIndex prefixIndex literals) := by
  induction literals generalizing prefixIndex with
  | nil => simp [gateList]
  | cons literal remaining ih =>
    rw [gateList, allDistinct_append]
    refine ⟨orGate_allDistinct _ _ _ ?_ ?_ ?_ ?_ ?_ ?_,
      ih (prefixIndex + 1)⟩
    · exact sourceVariable_ne_accumulatorVariable
        literal.1 clauseIndex (prefixIndex + 1)
    · exact sourceVariable_ne_accumulatorVariable
        literal.1 clauseIndex prefixIndex
    · exact Ne.symm
        (consecutive_accumulatorVariables_ne clauseIndex prefixIndex)
    · exact sourceVariable_ne_paddingVariable₀ literal.1
    · exact accumulatorVariable_ne_paddingVariable₀
        clauseIndex (prefixIndex + 1)
    · exact accumulatorVariable_ne_paddingVariable₀
        clauseIndex prefixIndex
end GapCVP.ThreeCNFReduction
