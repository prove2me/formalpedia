-- Prove2me | solution 1 for DeletionCode.RuleReconstruction.rules_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:14:30.427289+00:00
-- url     : https://prove2.me/submissions/5c2b73c7-cc16-45a7-8327-c90373aad1a5

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_RecordSerialization
import Definitions.Def_DeletionCode_RuleReconstruction
import Theorems.Thm_DeletionCode_RuleReconstruction_recovered_rule_spectrum

set_option autoImplicit true
open DeletionCode DeletionCode.RuleReconstruction
open Windows HeaderRecovery RootSelection SignedSupport RecordSerialization GeneratingModel
open scoped BigOperators
namespace DeletionCode.RuleReconstruction
theorem _root_.solution {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) : rulesOfData k group (dataOfFamily E) = rulesOfFamily E group := by
  classical
  unfold rulesOfData rulesOfFamily
  apply Finset.image_congr
  intro r hr
  exact recovered_rule_spectrum E (fun b => (group b).val) (groupBubbles group r)
end DeletionCode.RuleReconstruction
