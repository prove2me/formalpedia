-- Prove2me | solution 1 for DeletionCode.WitnessCost.length_le_two_pow_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:57.938049+00:00
-- url     : https://prove2.me/submissions/2838e7b4-b68b-45f4-9f85-c5f980a01b55

import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_WitnessCost

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCost
open HeaderRecovery UniqueWordParameters
namespace DeletionCode.WitnessCost
theorem _root_.solution (n : ℕ) :
    n ≤ 2 ^ windowLength (uniquenessLength n) := by
  have hclog : Nat.clog 2 n ≤ windowLength (uniquenessLength n) := by
    dsimp [windowLength, uniquenessLength]
    omega
  exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp hclog
end DeletionCode.WitnessCost
