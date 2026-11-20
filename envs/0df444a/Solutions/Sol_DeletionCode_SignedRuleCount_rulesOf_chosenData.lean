-- Prove2me | solution 1 for DeletionCode.SignedRuleCount.rulesOf_chosenData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:42.546684+00:00
-- url     : https://prove2.me/submissions/61608e42-2137-4e73-9359-d7b03e348049

import Definitions.Def_DeletionCode_RuleReconstruction
import Definitions.Def_DeletionCode_GeneratingCount
import Definitions.Def_DeletionCode_SignedRuleCount

set_option autoImplicit true
open DeletionCode DeletionCode.SignedRuleCount
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RecordSerialization GeneratingCount DescriptionCount
namespace DeletionCode.SignedRuleCount
theorem _root_.solution (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q}) :
    rulesOfData k group (chooseRuleData x n k ν R c group Q).val = Q.val :=
  (Classical.choose_spec (ruleSet_data_exists x n k ν R c group Q.val Q.property)).2
end DeletionCode.SignedRuleCount
