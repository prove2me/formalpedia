-- Prove2me | solution 1 for Champernowne.filter_blockAt_partial_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:34.520348+00:00
-- url     : https://prove2.me/submissions/ec428825-8430-49cc-93b6-ca1d51257b88

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Theorems.Thm_Champernowne_length_bigDigits_eq
public import Theorems.Thm_Champernowne_block_eq_iff

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (K t j : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hjk : j + w.length ≤ K + 1)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    (Finset.Ico (b ^ K) (b ^ K + t)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)
      = (Finset.Ico (b ^ K) (b ^ K + t)).filter
      (fun n => n / b ^ (K + 1 - j - w.length) % b ^ w.length
        = Nat.ofDigits b w.reverse) := by
  apply Finset.filter_congr
  intro n hn
  rw [Finset.mem_Ico] at hn
  exact block_eq_iff hb (length_bigDigits_eq (m := K + 1) hb hn.1 (by omega)) hw
    (by omega)
end Champernowne
