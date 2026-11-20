-- Prove2me | solution 1 for DeletionCode.SignedRuleCount.generatingRuleSet_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:15.525715+00:00
-- url     : https://prove2.me/submissions/ce19e767-8003-476e-89ea-8a49198ec33d

import Definitions.Def_DeletionCode_RuleReconstruction
import Definitions.Def_DeletionCode_GeneratingCount
import Definitions.Def_DeletionCode_SignedRuleCount
import Theorems.Thm_DeletionCode_SignedRuleCount_chooseRuleData_injective
import Theorems.Thm_DeletionCode_GeneratingCount_generatingData_finite


set_option autoImplicit true
open DeletionCode DeletionCode.SignedRuleCount
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RecordSerialization GeneratingCount DescriptionCount
namespace DeletionCode.SignedRuleCount
theorem _root_.solution (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Finite {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} := by
  let : Finite {data : RecoveredData ν // GeneratingData x n k ν c data} :=
    generatingData_finite x n k ν c hν hx
  exact Finite.of_injective (chooseRuleData x n k ν R c group)
    (chooseRuleData_injective x n k ν R c group)
end DeletionCode.SignedRuleCount
