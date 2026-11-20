-- Prove2me | solution 1 for DeletionCode.WitnessCost.linear_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:06.404294+00:00
-- url     : https://prove2.me/submissions/013457bb-eef4-4d2f-bece-d5a10ba7da7f

import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_WitnessCost
import Theorems.Thm_DeletionCode_WitnessCost_linear_le_power

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCost
open HeaderRecovery UniqueWordParameters
namespace DeletionCode.WitnessCost
theorem _root_.solution (t L R : ℕ) (hL : 4 * t + 2 ≤ L) :
    2 * t * R + 1 ≤ L ^ R := by
  calc
    _ ≤ (2 * t + 1) ^ R := linear_le_power (2 * t) R
    _ ≤ L ^ R := Nat.pow_le_pow_left (by omega) R
end DeletionCode.WitnessCost
