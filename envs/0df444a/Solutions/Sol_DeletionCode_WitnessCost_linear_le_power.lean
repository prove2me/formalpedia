-- Prove2me | solution 1 for DeletionCode.WitnessCost.linear_le_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:57.090875+00:00
-- url     : https://prove2.me/submissions/77db2a40-e245-4325-b6f1-fe8d34af17b3

import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_WitnessCost

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCost
open HeaderRecovery UniqueWordParameters
namespace DeletionCode.WitnessCost
theorem _root_.solution (c R : ℕ) : c * R + 1 ≤ (c + 1) ^ R := by
  induction R with
  | zero => simp
  | succ R ih =>
      calc
        c * (R + 1) + 1 ≤ (c * R + 1) * (c + 1) := by
          have hnonneg : 0 ≤ c * c * R := Nat.zero_le _
          nlinarith
        _ ≤ (c + 1) ^ R * (c + 1) := Nat.mul_le_mul_right _ ih
        _ = (c + 1) ^ (R + 1) := (pow_succ _ _).symm
end DeletionCode.WitnessCost
