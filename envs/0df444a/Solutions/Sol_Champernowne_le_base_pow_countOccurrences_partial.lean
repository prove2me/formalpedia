-- Prove2me | solution 1 for Champernowne.le_base_pow_countOccurrences_partial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:25.129465+00:00
-- url     : https://prove2.me/submissions/65c2cf4a-2690-4d71-9158-70f40fdd3d4b

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Theorems.Thm_Champernowne_sum_length_partial
public import Theorems.Thm_Champernowne_le_sum_countOccurrences_partial_cohort
public import Theorems.Thm_Champernowne_linear_le_const_mul_pow

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (K t : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hk : w.length ≤ K + 1)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), (bigDigits b n).length)
      ≤ b ^ w.length * (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
        + 3 * (w.length + 1) * b ^ (K + 1) := by
  have hwlen : 0 < w.length := List.length_pos_of_ne_nil hwne
  have hsum := le_sum_countOccurrences_partial_cohort hb K t hw hk hAt
  have hmul := Nat.mul_le_mul_left (b ^ w.length) hsum
  rw [Nat.mul_add] at hmul
  have hbpow : b ^ w.length * (2 * b ^ (K + 1 - w.length)) = 2 * b ^ (K + 1) := by
    rw [show b ^ w.length * (2 * b ^ (K + 1 - w.length))
        = 2 * (b ^ w.length * b ^ (K + 1 - w.length)) from by ring, ← pow_add]
    congr 2; omega
  have hlen := sum_length_partial hb K t hAt
  have hdm : b ^ w.length * (t / b ^ w.length) + t % b ^ w.length = t :=
    Nat.div_add_mod t (b ^ w.length)
  have hmod : t % b ^ w.length ≤ b ^ w.length := le_of_lt (Nat.mod_lt t (by positivity))
  have hlin := linear_le_const_mul_pow hb w.length (K + 1 - w.length)
  have hj : w.length + (K + 1 - w.length) + 1 = K + 2 := by omega
  rw [hj] at hlin
  have hpoweq : b ^ (K + 1 - w.length) * b ^ w.length = b ^ (K + 1) := by
    rw [← pow_add]; congr 1; omega
  have hrbound : (K + 1 - w.length) * (t % b ^ w.length) ≤ (w.length + 1) * b ^ (K + 1) := by
    calc (K + 1 - w.length) * (t % b ^ w.length)
        ≤ (K + 2) * b ^ w.length := Nat.mul_le_mul (by omega) hmod
    _ ≤ (w.length + 1) * b ^ (K + 1 - w.length) * b ^ w.length :=
        Nat.mul_le_mul_right _ hlin
    _ = (w.length + 1) * (b ^ (K + 1 - w.length) * b ^ w.length) := by ring
    _ = (w.length + 1) * b ^ (K + 1) := by rw [hpoweq]
  have htw : t * w.length ≤ (w.length + 1) * b ^ (K + 1) := by
    have ht1 : t ≤ b ^ (K + 1) := by omega
    calc t * w.length ≤ b ^ (K + 1) * w.length := Nat.mul_le_mul_right _ ht1
    _ ≤ b ^ (K + 1) * (w.length + 1) := Nat.mul_le_mul_left _ (by omega)
    _ = (w.length + 1) * b ^ (K + 1) := by ring
  have hkey : t * (K + 1) = (K + 1 - w.length) * (b ^ w.length * (t / b ^ w.length))
      + (K + 1 - w.length) * (t % b ^ w.length) + t * w.length := by
    have h2 : (K + 1 - w.length) * (b ^ w.length * (t / b ^ w.length))
        + (K + 1 - w.length) * (t % b ^ w.length) = (K + 1 - w.length) * t := by
      rw [← Nat.mul_add, hdm]
    have h3 : (K + 1 - w.length) * t + t * w.length = t * (K + 1) := by
      have hKw : (K + 1 - w.length) + w.length = K + 1 := by omega
      calc (K + 1 - w.length) * t + t * w.length
          = t * ((K + 1 - w.length) + w.length) := by ring
      _ = t * (K + 1) := by rw [hKw]
    omega
  have hcomm : b ^ w.length * ((K + 1 - w.length) * (t / b ^ w.length))
      = (K + 1 - w.length) * (b ^ w.length * (t / b ^ w.length)) := by ring
  have e1 : (K + 1 - w.length) * (b ^ w.length * (t / b ^ w.length))
      ≤ b ^ w.length * (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
        + b ^ w.length * (2 * b ^ (K + 1 - w.length)) := by
    rw [← hcomm]; exact hmul
  have hscale3 : 2 * b ^ (K + 1) ≤ (w.length + 1) * b ^ (K + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  calc (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), (bigDigits b n).length)
      = t * (K + 1) := hlen
  _ = (K + 1 - w.length) * (b ^ w.length * (t / b ^ w.length))
      + (K + 1 - w.length) * (t % b ^ w.length) + t * w.length := hkey
  _ ≤ (b ^ w.length * (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
      + b ^ w.length * (2 * b ^ (K + 1 - w.length)))
      + (w.length + 1) * b ^ (K + 1) + (w.length + 1) * b ^ (K + 1) :=
    Nat.add_le_add (Nat.add_le_add e1 hrbound) htw
  _ = b ^ w.length * (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
      + (b ^ w.length * (2 * b ^ (K + 1 - w.length))
        + (w.length + 1) * b ^ (K + 1) + (w.length + 1) * b ^ (K + 1)) := by ring
  _ = b ^ w.length * (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
      + (2 * b ^ (K + 1) + (w.length + 1) * b ^ (K + 1) + (w.length + 1) * b ^ (K + 1)) := by
    rw [hbpow]
  _ ≤ b ^ w.length * (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
      + 3 * (w.length + 1) * b ^ (K + 1) := by
    have hseq : 3 * (w.length + 1) * b ^ (K + 1)
        = (w.length + 1) * b ^ (K + 1) + (w.length + 1) * b ^ (K + 1)
          + (w.length + 1) * b ^ (K + 1) := by ring
    omega
end Champernowne
