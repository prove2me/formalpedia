-- Prove2me | solution 1 for Champernowne.card_blockAt_head_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:15.04284+00:00
-- url     : https://prove2.me/submissions/ef67f570-8da4-4892-8f83-3c5fa71230c5

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_block_eq_iff
public import Theorems.Thm_Champernowne_length_bigDigits_eq


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (m : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hw0 : w.head? = some 0) (hk : w.length ≤ m) :
    ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop 0).take w.length = w)).card = 0 := by
  rcases w with _ | ⟨d, w'⟩
  · simp at hw0
  · simp only [List.head?_cons, Option.some_inj] at hw0
    subst hw0
    have hlc : (0 :: w').length = w'.length + 1 := rfl
    have hD : Nat.ofDigits b (0 :: w').reverse < b ^ w'.length := by
      rw [List.reverse_cons, Nat.ofDigits_append]
      have h := Nat.ofDigits_lt_base_pow_length hb
        (fun d hd => hw d (List.mem_cons_of_mem _ (List.mem_reverse.mp hd)))
      rw [List.length_reverse] at h
      simpa [Nat.ofDigits] using h
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [block_eq_iff hb (length_bigDigits_eq hb hn.1 hn.2) hw (by omega)]
    intro hcontra
    have hP : 0 < b ^ (m - 0 - (0 :: w').length) := pow_pos (by omega) _
    have hup : b ^ (0 :: w').length * b ^ (m - 0 - (0 :: w').length)
        = b ^ m := by
      rw [← pow_add]; congr 1
      simp only [List.length_cons]
      omega
    have hdiv : n / b ^ (m - 0 - (0 :: w').length)
        < b ^ (0 :: w').length := by
      rw [Nat.div_lt_iff_lt_mul hP]
      omega
    have hlo1 : b ^ ((0 :: w').length - 1) * b ^ (m - 0 - (0 :: w').length)
        = b ^ (m - 1) := by
      rw [← pow_add]; congr 1
      simp only [List.length_cons]
      omega
    have hdivlo : b ^ ((0 :: w').length - 1)
        ≤ n / b ^ (m - 0 - (0 :: w').length) := by
      rw [Nat.le_div_iff_mul_le hP]
      omega
    rw [Nat.mod_eq_of_lt hdiv] at hcontra
    have hlen1 : (0 :: w').length - 1 = w'.length := by
      omega
    rw [hlen1] at hdivlo
    omega
end Champernowne
