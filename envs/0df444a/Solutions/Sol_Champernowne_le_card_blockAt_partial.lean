-- Prove2me | solution 1 for Champernowne.le_card_blockAt_partial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:11.590762+00:00
-- url     : https://prove2.me/submissions/be80d76b-3a07-4972-b2d7-22beeb3c8e51

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Theorems.Thm_Champernowne_le_card_Ico_filter_div_mod
public import Theorems.Thm_Champernowne_div_le_div_mul_add
public import Theorems.Thm_Champernowne_filter_blockAt_partial_congr

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (K t j : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hj : 0 < j) (hjk : j + w.length ≤ K + 1)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    t / b ^ w.length ≤ ((Finset.Ico (b ^ K) (b ^ K + t)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)).card
      + b ^ (K + 1 - j - w.length) := by
  rw [filter_blockAt_partial_congr hb K t j hw hjk hAt]
  have hD : Nat.ofDigits b w.reverse < b ^ w.length := by
    have h := Nat.ofDigits_lt_base_pow_length hb
      (fun d hd => hw d (List.mem_reverse.mp hd))
    rwa [List.length_reverse] at h
  have hp : 0 < b ^ (K + 1 - j - w.length) := pow_pos (by omega) _
  have hq : 0 < b ^ w.length := pow_pos (by omega) _
  have hpq : b ^ (K + 1 - j - w.length) * b ^ w.length = b ^ (K + 1 - j) := by
    rw [← pow_add]; congr 1; omega
  have hdvd : b ^ (K + 1 - j - w.length) * b ^ w.length ∣ b ^ K :=
    hpq ▸ pow_dvd_pow b (by omega)
  calc t / b ^ w.length
      ≤ t / (b ^ (K + 1 - j - w.length) * b ^ w.length)
        * b ^ (K + 1 - j - w.length) + b ^ (K + 1 - j - w.length) :=
      div_le_div_mul_add t _ (b ^ w.length) hp hq
  _ ≤ _ := Nat.add_le_add_right
      (le_card_Ico_filter_div_mod hp hq hD hdvd) _
end Champernowne
