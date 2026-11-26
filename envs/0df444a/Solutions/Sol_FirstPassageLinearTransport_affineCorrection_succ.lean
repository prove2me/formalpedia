-- Prove2me | solution 1 for FirstPassageLinearTransport.affineCorrection_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:24.934261+00:00
-- url     : https://prove2.me/submissions/8fffbd4f-f8cd-4ce4-9c25-cdd83288a8ef

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Theorems.Thm_FirstPassageLinearTransport_oddCount_mono
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_succ
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
    affineCorrection n (k + 1) =
      3 ^ (parityBit n k : ℕ) * affineCorrection n k +
        (parityBit n k : ℕ) * 2 ^ k := by
  rw [affineCorrection, Finset.sum_range_succ, affineCorrection]
  simp only [Nat.sub_self, pow_zero, mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i + 1 ≤ k := by
    simpa using Finset.mem_range.mp hi
  have hmono : oddCount n (i + 1) ≤ oddCount n k :=
    oddCount_mono hik
  have hexponent :
      oddCount n (k + 1) - oddCount n (i + 1) =
        (oddCount n k - oddCount n (i + 1)) + (parityBit n k : ℕ) := by
    rw [oddCount_succ]
    omega
  rw [hexponent, pow_add]
  ring
end FirstPassageLinearTransport
