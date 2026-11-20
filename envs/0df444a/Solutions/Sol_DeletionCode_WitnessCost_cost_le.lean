-- Prove2me | solution 1 for DeletionCode.WitnessCost.cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:33.878203+00:00
-- url     : https://prove2.me/submissions/fc2ed987-8ff1-4f8d-b4fa-49839b41ee76

import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_WitnessCost
import Theorems.Thm_DeletionCode_WitnessCost_size_le_cube
import Theorems.Thm_DeletionCode_WitnessCost_linear_factor_le

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCost
open HeaderRecovery UniqueWordParameters
namespace DeletionCode.WitnessCost
theorem _root_.solution (t L R : ℕ) (hL : 4 * t + 2 ≤ L)
    (hR : R ≤ 1 + 4 * t * L ^ 2) :
    2 ^ R * (2 * t * R + 1) * (L * R) ^ (CountExponent.exponent t * R) ≤
      L ^ (exponent t * R) := by
  have htwo : 2 ^ R ≤ L ^ R := Nat.pow_le_pow_left (by omega) R
  have hlinear := linear_factor_le t L R hL
  have hprod : L * R ≤ L ^ 4 := by
    calc
      L * R ≤ L * L ^ 3 := Nat.mul_le_mul_left _ (size_le_cube t L R hL hR)
      _ = L ^ 4 := by ring
  have hpower : (L * R) ^ (CountExponent.exponent t * R) ≤
      (L ^ 4) ^ (CountExponent.exponent t * R) :=
    Nat.pow_le_pow_left hprod _
  calc
    _ ≤ L ^ R * L ^ R * (L ^ 4) ^ (CountExponent.exponent t * R) :=
      Nat.mul_le_mul (Nat.mul_le_mul htwo hlinear) hpower
    _ = L ^ (exponent t * R) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      unfold exponent
      ring
end DeletionCode.WitnessCost
