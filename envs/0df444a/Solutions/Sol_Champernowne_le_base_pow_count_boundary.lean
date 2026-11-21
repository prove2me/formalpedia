-- Prove2me | solution 1 for Champernowne.le_base_pow_count_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:12.047654+00:00
-- url     : https://prove2.me/submissions/63a15b67-350f-49fe-b53f-b378a479adcc

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Theorems.Thm_Champernowne_sum_length_partial
public import Theorems.Thm_Champernowne_le_base_pow_countOccurrences_partial
public import Theorems.Thm_Champernowne_cohort_error_add_le

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (K : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    (∑ n ∈ Finset.Ico 1 (b ^ K), (bigDigits b n).length)
      ≤ b ^ w.length * (∑ n ∈ Finset.Ico 1 (b ^ K), countOccurrences w (bigDigits b n))
        + 6 * (w.length + 1) * b ^ K := by
  have hwlen : 0 < w.length := List.length_pos_of_ne_nil hwne
  induction K with
  | zero => simp
  | succ K ih =>
    have h1 : b ^ K ≤ b ^ (K + 1) :=
      Nat.pow_le_pow_right (by omega) (Nat.le_add_right K 1)
    have hcov : b ^ K + (b ^ (K + 1) - b ^ K) = b ^ (K + 1) := by omega
    rw [← Finset.sum_Ico_consecutive (fun n => countOccurrences w (bigDigits b n))
        (Nat.one_le_pow K b (by omega)) h1,
      ← Finset.sum_Ico_consecutive (fun n => (bigDigits b n).length)
        (Nat.one_le_pow K b (by omega)) h1,
      Nat.mul_add]
    rcases Nat.lt_or_ge (K + 1) w.length with hshort | hlong
    · -- cohort shorter than `w`: drop the count, bound the length crudely
      have hlen := sum_length_partial hb K (b ^ (K + 1) - b ^ K) (by omega)
      rw [hcov] at hlen
      have hbnd : (b ^ (K + 1) - b ^ K) * (K + 1) ≤ (w.length + 1) * b ^ (K + 1) := by
        calc (b ^ (K + 1) - b ^ K) * (K + 1)
            ≤ b ^ (K + 1) * (K + 1) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ b ^ (K + 1) * (w.length + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (w.length + 1) * b ^ (K + 1) := Nat.mul_comm _ _
      have hscale : 6 * (w.length + 1) * b ^ K + (w.length + 1) * b ^ (K + 1)
          ≤ 6 * (w.length + 1) * b ^ (K + 1) := by
        have h := cohort_error_add_le hb (w.length + 1) K
        nlinarith only [h, Nat.zero_le ((w.length + 1) * b ^ (K + 1))]
      omega
    · have hpart := le_base_pow_countOccurrences_partial hb K (b ^ (K + 1) - b ^ K)
        hw hwne (by omega) (by omega)
      rw [hcov] at hpart
      have hscale := cohort_error_add_le hb (w.length + 1) K
      omega
end Champernowne
