-- Prove2me | solution 1 for Champernowne.card_blockAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:42.489881+00:00
-- url     : https://prove2.me/submissions/55f55a68-cf1d-47e0-a92e-bb13dfac5b22

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_card_Ico_filter_div_mod
public import Theorems.Thm_Champernowne_block_eq_iff
public import Theorems.Thm_Champernowne_length_bigDigits_eq


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (m j : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hj : 0 < j) (hjk : j + w.length ≤ m) :
    ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)).card
      = (b - 1) * b ^ (m - w.length - 1) := by
  have hD : Nat.ofDigits b w.reverse < b ^ w.length := by
    have h := Nat.ofDigits_lt_base_pow_length hb
      (fun d hd => hw d (List.mem_reverse.mp hd))
    rwa [List.length_reverse] at h
  have hcongr : (Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)
      = (Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => n / b ^ (m - j - w.length) % b ^ w.length
        = Nat.ofDigits b w.reverse) := by
    apply Finset.filter_congr
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact block_eq_iff hb (length_bigDigits_eq hb hn.1 hn.2) hw hjk
  have hpq : b ^ (m - j - w.length) * b ^ w.length = b ^ (m - j) := by
    rw [← pow_add]; congr 1; omega
  rw [hcongr, card_Ico_filter_div_mod (pow_pos (by omega) _)
    (pow_pos (by omega) _) hD (hpq ▸ pow_dvd_pow b (by omega))
    (hpq ▸ pow_dvd_pow b (by omega)), hpq,
    Nat.pow_div (by omega) (by omega), Nat.pow_div (by omega) (by omega)]
  have h1 : b ^ (m - (m - j)) = b * b ^ (m - 1 - (m - j)) := by
    rw [← pow_succ']; congr 1; omega
  have h2 : b ^ (m - 1 - (m - j)) * b ^ (m - j - w.length)
      = b ^ (m - w.length - 1) := by
    rw [← pow_add]; congr 1; omega
  have hbr : (b - 1) * b ^ (m - 1 - (m - j)) + b ^ (m - 1 - (m - j))
      = b * b ^ (m - 1 - (m - j)) := by
    have hb1 : b - 1 + 1 = b := by omega
    calc (b - 1) * b ^ (m - 1 - (m - j)) + b ^ (m - 1 - (m - j))
        = (b - 1 + 1) * b ^ (m - 1 - (m - j)) := by ring
    _ = b * b ^ (m - 1 - (m - j)) := by rw [hb1]
  rw [h1, show b * b ^ (m - 1 - (m - j)) - b ^ (m - 1 - (m - j))
      = (b - 1) * b ^ (m - 1 - (m - j)) by omega,
    Nat.mul_assoc, h2]
end Champernowne
