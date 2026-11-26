-- Prove2me | solution 1 for FirstPassageLinearTransport.exact_affine_iterate_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:39.716897+00:00
-- url     : https://prove2.me/submissions/595def31-a9ca-4f76-9552-07519c2c957f

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Theorems.Thm_FirstPassageLinearTransport_exact_affine_iterate_scaled
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
    (orbit k n : ℝ) =
      (3 : ℝ) ^ (oddCount n k) / (2 : ℝ) ^ k * (n : ℝ) +
        ∑ i ∈ Finset.range k,
          ((parityBit n i : ℕ) : ℝ) *
            (3 : ℝ) ^ (oddCount n k - oddCount n (i + 1)) /
              (2 : ℝ) ^ (k - i) := by
  have hcorrection :
      (affineCorrection n k : ℝ) / (2 : ℝ) ^ k =
        ∑ i ∈ Finset.range k,
          ((parityBit n i : ℕ) : ℝ) *
            (3 : ℝ) ^ (oddCount n k - oddCount n (i + 1)) /
              (2 : ℝ) ^ (k - i) := by
    unfold affineCorrection
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
  rw [← hcorrection]
  rw [div_mul_eq_mul_div, ← add_div]
  have hpow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  apply (eq_div_iff hpow).2
  have hscaled :
      (2 : ℝ) ^ k * (orbit k n : ℝ) =
        (3 : ℝ) ^ (oddCount n k) * (n : ℝ) +
          (affineCorrection n k : ℝ) := by
    exact_mod_cast exact_affine_iterate_scaled n k
  simpa [mul_comm] using hscaled
end FirstPassageLinearTransport
