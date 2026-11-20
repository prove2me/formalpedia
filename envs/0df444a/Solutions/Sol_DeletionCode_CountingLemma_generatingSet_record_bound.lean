-- Prove2me | solution 1 for DeletionCode.CountingLemma.generatingSet_record_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:51.236238+00:00
-- url     : https://prove2.me/submissions/8ef89fbc-a7ce-4e83-826c-123d05a525ec

import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_CountingLemma
import Theorems.Thm_DeletionCode_SignedRuleCount_generatingRuleSet_card_bound
import Theorems.Thm_DeletionCode_SignedRuleCount_generatingRuleSet_finite


set_option autoImplicit true
open DeletionCode DeletionCode.CountingLemma
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RuleSetGraph SignedRuleCount DescriptionCount CountExponent
namespace DeletionCode.CountingLemma
theorem _root_.solution (x : Letters) (n k ν R c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet k // GeneratingSet x n k ν R c group Q} ≤
      n ^ c * fieldBound (windowLength k) ν ^ (50 * ν) := by
  let : Finite {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} :=
    generatingRuleSet_finite x n k ν R c group hν hx
  have hcard := Nat.card_le_card_of_injective (generatingSetInclusion x n k ν R c group)
    (fun _ _ h => Subtype.ext (congrArg (fun Q : {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} => Q.val) h))
  exact hcard.trans (generatingRuleSet_card_bound x n k ν R c group hν hx)
end DeletionCode.CountingLemma
