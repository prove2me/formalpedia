-- Prove2me | solution 1 for Champernowne.le_base_pow_countOccurrences_champPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:21.544465+00:00
-- url     : https://prove2.me/submissions/2ec7a14d-b1db-4381-a4f7-090af14fafea

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Theorems.Thm_Champernowne_n_lt_length_champIndex_add
public import Theorems.Thm_Champernowne_length_bigDigits_champIndex_succ_le
public import Theorems.Thm_Champernowne_le_countOccurrences_champPrefix
public import Theorems.Thm_Champernowne_le_base_pow_countOccurrences_champBlocks
public import Theorems.Thm_Champernowne_length_champBlocks
public import Theorems.Thm_Champernowne_linear_le_const_mul_pow
public import Theorems.Thm_Champernowne_sum_le_countOccurrences_champBlocks


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (n M : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hM : 0 < M) (hwM : w.length ≤ M)
    (h1 : b ^ (M - 1) ≤ champIndex b n + 1) (h2 : champIndex b n + 1 ≤ b ^ M) :
    n ≤ b ^ w.length * countOccurrences w (champPrefix b n)
      + 7 * (w.length + 1) * b ^ w.length * b ^ M := by
  have hS := sum_le_countOccurrences_champBlocks (b := b) hwne (champIndex b n)
  have hDig := le_base_pow_countOccurrences_champBlocks hb (champIndex b n) M hw hwne hM hwM h1 h2
  have hlen := n_lt_length_champIndex_add b n
  have hstraddle := length_bigDigits_champIndex_succ_le hb h2
  have hle := le_countOccurrences_champPrefix b n hwne (w := w)
  have hMpow : M + 1 ≤ b ^ M := by
    have h0 := linear_le_const_mul_pow hb 0 M; simpa using h0
  rw [length_champBlocks] at hlen
  have hSmul : b ^ w.length
      * (∑ n ∈ Finset.Ico 1 (champIndex b n + 1), countOccurrences w (bigDigits b n))
      ≤ b ^ w.length * countOccurrences w (champBlocks b (champIndex b n)) :=
    Nat.mul_le_mul_left _ hS
  have hlemul : b ^ w.length * countOccurrences w (champBlocks b (champIndex b n))
      ≤ b ^ w.length * countOccurrences w (champPrefix b n) :=
    Nat.mul_le_mul_left _ hle
  have hp : 1 ≤ b ^ w.length := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hMscale : M + 1 ≤ b ^ w.length * b ^ M := by
    calc M + 1 ≤ b ^ M := hMpow
    _ = 1 * b ^ M := by ring
    _ ≤ b ^ w.length * b ^ M := Nat.mul_le_mul_right _ hp
  have hbudget : 6 * (w.length + 1) * b ^ M + b ^ w.length * b ^ M
      ≤ 7 * (w.length + 1) * b ^ w.length * b ^ M := by
    have e0 : 6 * (w.length + 1) * b ^ M ≤ 6 * (w.length + 1) * b ^ w.length * b ^ M := by
      calc 6 * (w.length + 1) * b ^ M = 6 * (w.length + 1) * 1 * b ^ M := by ring
      _ ≤ 6 * (w.length + 1) * b ^ w.length * b ^ M :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
    have e1 : b ^ w.length * b ^ M ≤ (w.length + 1) * b ^ w.length * b ^ M := by
      have hh : b ^ w.length ≤ (w.length + 1) * b ^ w.length :=
        Nat.le_mul_of_pos_left _ (by omega)
      exact Nat.mul_le_mul_right _ hh
    have e2 : 6 * (w.length + 1) * b ^ w.length * b ^ M + (w.length + 1) * b ^ w.length * b ^ M
        = 7 * (w.length + 1) * b ^ w.length * b ^ M := by ring
    omega
  omega
end Champernowne
