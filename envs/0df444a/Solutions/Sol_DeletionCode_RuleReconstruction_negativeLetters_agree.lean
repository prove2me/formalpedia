-- Prove2me | solution 1 for DeletionCode.RuleReconstruction.negativeLetters_agree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:03:58.03648+00:00
-- url     : https://prove2.me/submissions/dd186cec-ac5c-4fcb-92b5-3a1dc623536b

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_RecordSerialization
import Definitions.Def_DeletionCode_RuleReconstruction

set_option autoImplicit true
open DeletionCode DeletionCode.RuleReconstruction
open Windows HeaderRecovery RootSelection SignedSupport RecordSerialization GeneratingModel
open scoped BigOperators
namespace DeletionCode.RuleReconstruction
theorem _root_.solution {ν k : ℕ} (E : EditedFamily (Fin ν) k) (b : Fin ν) :
    Agree (negativeLetters (dataOfFamily E) b) 0
      (negativePath k (E.header b) (E.long b)) 0 (negativeLength k (E.header b)) := by
  intro i hi
  simp [negativeLetters, dataOfFamily, dataOfOutput, List.getD, hi]
end DeletionCode.RuleReconstruction
