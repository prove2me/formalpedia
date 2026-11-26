-- Prove2me | solution 1 for FirstPassageLinearTransport.normalizedCorrectionTerm_scaled_le_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:52.181326+00:00
-- url     : https://prove2.me/submissions/616803b8-06b7-429c-ac14-f0900c6c7543

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_parityDigitR_le_one
import Theorems.Thm_FirstPassageLinearTransport_oddCount_lower_of_maximalRegular
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n M k i : ℕ} {h : ℝ}
    (hik : i < k) (hkM : k ≤ M)
    (hreg : MaximalParityRegular n M h) :
    normalizedCorrectionTerm k n i * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
      (3 : ℝ) ^ h / 2 * rho ^ (k - 1 - i) := by
  have hiM : i + 1 ≤ M := by omega
  have hS := oddCount_lower_of_maximalRegular hreg hiM
  have hki : k = (i + 1) + (k - 1 - i) := by omega
  have hExp :
      (k : ℝ) / 2 ≤
        oddCount n (i + 1) + h + ((k - 1 - i : ℕ) : ℝ) / 2 := by
    have hkiR :
        (k : ℝ) = (i + 1 : ℕ) + (k - 1 - i : ℕ) := by
      exact_mod_cast hki
    push_cast at hS hkiR
    nlinarith
  have hbase :
      (3 : ℝ) ^ ((k : ℝ) / 2) ≤
        (3 : ℝ) ^ oddCount n (i + 1) *
          (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) := by
    calc
      (3 : ℝ) ^ ((k : ℝ) / 2) ≤
          (3 : ℝ) ^
            ((oddCount n (i + 1) : ℝ) + h +
              ((k - 1 - i : ℕ) : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
      _ = (3 : ℝ) ^ oddCount n (i + 1) *
          (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
          Real.rpow_natCast]
  have hden :
      0 < (3 : ℝ) ^ oddCount n (i + 1) * (2 : ℝ) ^ (k - i) := by
    positivity
  have hraw :
      normalizedCorrectionTerm k n i * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
        (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) /
            (2 : ℝ) ^ (k - i) := by
    unfold normalizedCorrectionTerm
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    calc
      parityDigitR n i * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
          (3 : ℝ) ^ ((k : ℝ) / 2) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (parityDigitR_le_one n i)
            (Real.rpow_nonneg (by norm_num) _)
      _ ≤ (3 : ℝ) ^ oddCount n (i + 1) *
          (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) := hbase
      _ = ((3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) /
            (2 : ℝ) ^ (k - i)) *
          ((3 : ℝ) ^ oddCount n (i + 1) *
            (2 : ℝ) ^ (k - i)) := by
        field_simp
  calc
    _ ≤ (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) /
            (2 : ℝ) ^ (k - i) := hraw
    _ = (3 : ℝ) ^ h / 2 * rho ^ (k - 1 - i) := by
      have hd : k - i = (k - 1 - i) + 1 := by omega
      rw [hd, pow_succ, Real.rpow_div_two_eq_sqrt _ (by norm_num),
        Real.rpow_natCast]
      unfold rho
      rw [div_pow]
      field_simp
end FirstPassageLinearTransport
