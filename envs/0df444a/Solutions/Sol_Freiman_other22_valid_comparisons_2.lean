-- Prove2me | solution 2 for Freiman.other22_valid_comparisons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:08:09.792522+00:00
-- url     : https://prove2.me/submissions/61ffd50b-1544-41cc-affe-ca55e45c572f

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Freiman_other22_comparisons
import Theorems.Thm_Freiman_other22_all_bindings
import Theorems.Thm_Freiman_other22_all_witnesses

open Freiman

-- `other22_comparisons` isolates the two whole-catalogue obligations of the other22
-- comparison law; the witnesses half is already Proved, so only the bindings half
-- remains as a child.
theorem solution (k : Fin 6) (r s q : ℝ)
    (hm : certRectangleMem (other22Paths k).rectangle r s)
    (hsource : ∃ bs ∈ lowerHistorySourcePremises (other22Paths k),
      lowerHistoryConditions bs r s q) :
    lowerHistoryComparisonsHold (other22Paths k) r s q :=
  other22_comparisons k other22_all_bindings other22_all_witnesses r s q hm hsource
