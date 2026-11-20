-- Prove2me | solution 1 for DeletionCode.SignedRuleCount.chooseRuleData_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:43.855696+00:00
-- url     : https://prove2.me/submissions/a3d273c0-4ef8-4010-b076-72007ea68321

import Definitions.Def_DeletionCode_RuleReconstruction
import Definitions.Def_DeletionCode_GeneratingCount
import Definitions.Def_DeletionCode_SignedRuleCount
import Theorems.Thm_DeletionCode_SignedRuleCount_rulesOf_chosenData

set_option autoImplicit true
open DeletionCode DeletionCode.SignedRuleCount
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RecordSerialization GeneratingCount DescriptionCount
namespace DeletionCode.SignedRuleCount
theorem _root_.solution (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R) :
    Function.Injective (chooseRuleData x n k ν R c group) := by
  intro Q₁ Q₂ heq
  apply Subtype.ext
  calc
    Q₁.val = rulesOfData k group (chooseRuleData x n k ν R c group Q₁).val :=
      (rulesOf_chosenData x n k ν R c group Q₁).symm
    _ = rulesOfData k group (chooseRuleData x n k ν R c group Q₂).val :=
      congrArg (fun data : {data : RecoveredData ν // GeneratingData x n k ν c data} =>
        rulesOfData k group data.val) heq
    _ = Q₂.val := rulesOf_chosenData x n k ν R c group Q₂
end DeletionCode.SignedRuleCount
