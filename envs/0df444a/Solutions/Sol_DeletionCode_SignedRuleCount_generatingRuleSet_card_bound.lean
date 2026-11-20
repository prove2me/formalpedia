-- Prove2me | solution 1 for DeletionCode.SignedRuleCount.generatingRuleSet_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:00.700877+00:00
-- url     : https://prove2.me/submissions/092ecc9b-ea80-4d88-86c3-cc143ac2c58f

import Definitions.Def_DeletionCode_RuleReconstruction
import Definitions.Def_DeletionCode_GeneratingCount
import Definitions.Def_DeletionCode_SignedRuleCount
import Theorems.Thm_DeletionCode_SignedRuleCount_generatingRuleSet_card_le_data
import Theorems.Thm_DeletionCode_GeneratingCount_generatingData_card_bound


set_option autoImplicit true
open DeletionCode DeletionCode.SignedRuleCount
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RecordSerialization GeneratingCount DescriptionCount
namespace DeletionCode.SignedRuleCount
theorem _root_.solution (x : Letters) (n k ν R c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by
  exact (generatingRuleSet_card_le_data x n k ν R c group hν hx).trans
    (generatingData_card_bound x n k ν c hν hx)
end DeletionCode.SignedRuleCount
