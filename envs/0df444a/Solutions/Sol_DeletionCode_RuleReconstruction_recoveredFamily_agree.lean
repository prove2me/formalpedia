-- Prove2me | solution 1 for DeletionCode.RuleReconstruction.recoveredFamily_agree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:04:32.98184+00:00
-- url     : https://prove2.me/submissions/21834d5a-133d-4a57-b3b2-29e2f7a5161a

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_RecordSerialization
import Definitions.Def_DeletionCode_RuleReconstruction
import Theorems.Thm_DeletionCode_RuleReconstruction_negativeLetters_agree
import Theorems.Thm_DeletionCode_HeaderRecovery_rebuild_positive_from_known_negative


set_option autoImplicit true
open DeletionCode DeletionCode.RuleReconstruction
open Windows HeaderRecovery RootSelection SignedSupport RecordSerialization GeneratingModel
open scoped BigOperators
namespace DeletionCode.RuleReconstruction
theorem _root_.solution {ν k : ℕ} (E : EditedFamily (Fin ν) k)
    (rank : Fin ν → ℕ) (b : Fin ν) (side : Bool) :
    Agree ((recoveredFamily k rank (dataOfFamily E)).path b side) 0
      (E.family.path b side) 0 (windowLength k + E.family.extra b side) := by
  rw [← E.path_length_eq b side]
  cases side with
  | false => exact negativeLetters_agree E b
  | true =>
    exact rebuild_positive_from_known_negative k (E.header b) (E.long b)
      (negativeLetters (dataOfFamily E) b) (E.rho_lower b) (E.rho_upper b)
      (E.header_bit b) (negativeLetters_agree E b)
end DeletionCode.RuleReconstruction
