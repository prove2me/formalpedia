-- Prove2me | solution 1 for DeletionCode.WitnessCost.size_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:57.493515+00:00
-- url     : https://prove2.me/submissions/1c816176-c9ad-4737-9597-57f2c970c482

import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_WitnessCost

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCost
open HeaderRecovery UniqueWordParameters
namespace DeletionCode.WitnessCost
theorem _root_.solution (t L R : ℕ) (hL : 4 * t + 2 ≤ L)
    (hR : R ≤ 1 + 4 * t * L ^ 2) : R ≤ L ^ 3 := by
  have hsq : 1 ≤ L ^ 2 := one_le_pow₀ (by omega)
  calc
    R ≤ 1 + 4 * t * L ^ 2 := hR
    _ ≤ (4 * t + 1) * L ^ 2 := by nlinarith
    _ ≤ L * L ^ 2 := Nat.mul_le_mul_right _ (by omega)
    _ = L ^ 3 := by ring
end DeletionCode.WitnessCost
