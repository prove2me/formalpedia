-- Prove2me | solution 1 for DeletionCode.WitnessCost.length_le_two_pow_of_window_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:14.562957+00:00
-- url     : https://prove2.me/submissions/333e8bd1-0931-4fe0-869e-3681cf267ebd

import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_WitnessCost
import Theorems.Thm_DeletionCode_WitnessCost_length_le_two_pow_window

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCost
open HeaderRecovery UniqueWordParameters
namespace DeletionCode.WitnessCost
theorem _root_.solution (n R : ℕ)
    (hR : windowLength (uniquenessLength n) < R) : n ≤ 2 ^ R := by
  exact (length_le_two_pow_window n).trans
    (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.le_of_lt hR))
end DeletionCode.WitnessCost
