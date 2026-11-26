-- Prove2me | solution 1 for FirstPassageLinearTransport.exact_affine_iterate_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:03.870374+00:00
-- url     : https://prove2.me/submissions/9de874e8-6b7d-44d9-8157-a396aa19691f

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Theorems.Thm_FirstPassageLinearTransport_two_mul_shortcut
import Theorems.Thm_FirstPassageLinearTransport_affineCorrection_succ
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_succ
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_succ
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution (n k : ℕ) :
    2 ^ k * orbit k n =
      3 ^ (oddCount n k) * n + affineCorrection n k := by
  induction k with
  | zero => simp [affineCorrection]
  | succ k ih =>
      have hstep :
          2 * orbit (k + 1) n =
            3 ^ (parityBit n k : ℕ) * orbit k n +
              (parityBit n k : ℕ) := by
        rw [orbit_succ, two_mul_shortcut]
        rfl
      calc
        2 ^ (k + 1) * orbit (k + 1) n =
            2 ^ k * (2 * orbit (k + 1) n) := by
              rw [pow_succ]
              ring
        _ = 2 ^ k *
            (3 ^ (parityBit n k : ℕ) * orbit k n +
              (parityBit n k : ℕ)) := by rw [hstep]
        _ = 3 ^ (parityBit n k : ℕ) * (2 ^ k * orbit k n) +
              (parityBit n k : ℕ) * 2 ^ k := by ring
        _ = 3 ^ (parityBit n k : ℕ) *
              (3 ^ (oddCount n k) * n + affineCorrection n k) +
              (parityBit n k : ℕ) * 2 ^ k := by rw [ih]
        _ = 3 ^ (oddCount n (k + 1)) * n +
              affineCorrection n (k + 1) := by
                rw [oddCount_succ, affineCorrection_succ, pow_add]
                ring
end FirstPassageLinearTransport
