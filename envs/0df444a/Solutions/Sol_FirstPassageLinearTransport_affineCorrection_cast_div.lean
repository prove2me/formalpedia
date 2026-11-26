-- Prove2me | solution 1 for FirstPassageLinearTransport.affineCorrection_cast_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:25.966151+00:00
-- url     : https://prove2.me/submissions/96dedcf1-1c07-47f4-ac6c-7b1f230bb598

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
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
    (affineCorrection n k : ℚ) / (2 : ℚ) ^ k = affineCorrectionQ n k := by
  unfold affineCorrection affineCorrectionQ
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by
    exact Nat.le_of_lt (Finset.mem_range.mp hi)
  have hk : k = i + (k - i) := by omega
  rw [hk, pow_add]
  field_simp
  simp
end FirstPassageLinearTransport
