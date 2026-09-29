-- Prove2me | solution 1 for Freiman.other22_valid_comparisons
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:08:07.84379+00:00
-- url     : https://prove2.me/submissions/669be7d7-37b1-4db6-8e49-44600a8a4605

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Freiman_other22_comparisons
import Theorems.Thm_Freiman_other22_all_bindings
import Theorems.Thm_Freiman_other22_all_witnesses

open Freiman

theorem solution (k : Fin 6) (r s q : ℝ)
    (hm : certRectangleMem (other22Paths k).rectangle r s)
    (hsource : ∃ bs ∈ lowerHistorySourcePremises (other22Paths k), lowerHistoryConditions bs r s q) :
    lowerHistoryComparisonsHold (other22Paths k) r s q := by
  exact other22_comparisons k other22_all_bindings other22_all_witnesses r s q hm hsource
