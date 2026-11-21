-- Prove2me | solution 1 for Champernowne.le_base_pow_countOccurrences_champBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:47.170799+00:00
-- url     : https://prove2.me/submissions/5895ed90-e7a4-4ddb-936d-79f79e709e55

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Theorems.Thm_Champernowne_le_base_pow_countOccurrences_partial
public import Theorems.Thm_Champernowne_cohort_error_add_le
public import Theorems.Thm_Champernowne_le_base_pow_count_boundary

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (N M : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hM : 0 < M) (hwM : w.length ≤ M)
    (h1 : b ^ (M - 1) ≤ N + 1) (h2 : N + 1 ≤ b ^ M) :
    (∑ n ∈ Finset.Ico 1 (N + 1), (bigDigits b n).length)
      ≤ b ^ w.length * (∑ n ∈ Finset.Ico 1 (N + 1), countOccurrences w (bigDigits b n))
        + 6 * (w.length + 1) * b ^ M := by
  obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
  rw [show K + 1 - 1 = K from rfl] at h1
  obtain ⟨t, ht⟩ : ∃ t, N + 1 = b ^ K + t := ⟨N + 1 - b ^ K, by omega⟩
  have hAt : b ^ K + t ≤ b ^ (K + 1) := by omega
  rw [ht, ← Finset.sum_Ico_consecutive (fun n => countOccurrences w (bigDigits b n))
      (Nat.one_le_pow K b (by omega)) (Nat.le_add_right _ _),
    ← Finset.sum_Ico_consecutive (fun n => (bigDigits b n).length)
      (Nat.one_le_pow K b (by omega)) (Nat.le_add_right _ _),
    Nat.mul_add]
  have hbd := le_base_pow_count_boundary hb K hw hwne
  have hpart := le_base_pow_countOccurrences_partial hb K t hw hwne (by omega) hAt
  have hscale := cohort_error_add_le hb (w.length + 1) K
  omega
end Champernowne
