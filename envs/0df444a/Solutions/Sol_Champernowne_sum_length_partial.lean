-- Prove2me | solution 1 for Champernowne.sum_length_partial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:37:47.435645+00:00
-- url     : https://prove2.me/submissions/64467cc8-8b1f-4966-b8ff-03444584af82

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Theorems.Thm_Champernowne_length_bigDigits_eq

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (K t : ℕ)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    ∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), (bigDigits b n).length
      = t * (K + 1) := by
  have hc : ∀ n ∈ Finset.Ico (b ^ K) (b ^ K + t),
      (bigDigits b n).length = K + 1 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact length_bigDigits_eq hb (by simpa using hn.1) (by omega)
  rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico,
    Nat.add_sub_cancel_left, smul_eq_mul]
end Champernowne
