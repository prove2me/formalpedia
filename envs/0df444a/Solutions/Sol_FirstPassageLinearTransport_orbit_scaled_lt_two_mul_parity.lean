-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_scaled_lt_two_mul_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:39:16.752884+00:00
-- url     : https://prove2.me/submissions/b506195a-c9d7-4015-93e0-560d12df14af

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_affineCorrection_lt_two_pow_mul_three_pow
import Theorems.Thm_FirstPassageLinearTransport_exact_affine_iterate_scaled
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {m x j : ℕ} (hx : x ∈ dyadicShell m) (hj : j ≤ m) :
    2 ^ j * orbit j x < 2 * 3 ^ oddCount x j * x := by
  rw [exact_affine_iterate_scaled]
  have hcorr := affineCorrection_lt_two_pow_mul_three_pow x j
  have hjpow : 2 ^ j ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hj
  have hxm : 2 ^ m ≤ x := (mem_dyadicShell.mp hx).1
  have htwojx : 2 ^ j ≤ x := hjpow.trans hxm
  calc
    3 ^ oddCount x j * x + affineCorrection x j <
        3 ^ oddCount x j * x + 2 ^ j * 3 ^ oddCount x j :=
      Nat.add_lt_add_left hcorr _
    _ ≤ 3 ^ oddCount x j * x + x * 3 ^ oddCount x j := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right (3 ^ oddCount x j) htwojx) _
    _ = 2 * 3 ^ oddCount x j * x := by ring
end FirstPassageLinearTransport
