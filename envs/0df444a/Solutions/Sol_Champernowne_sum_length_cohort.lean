-- Prove2me | solution 1 for Champernowne.sum_length_cohort
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:01.334364+00:00
-- url     : https://prove2.me/submissions/9d018550-3ebf-482e-9694-39207b6e1e27

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Theorems.Thm_Champernowne_length_bigDigits_eq
public import Theorems.Thm_Champernowne_card_mDigit

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (m : ℕ) (hm : 0 < m) :
    ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m), (bigDigits b n).length
      = (b - 1) * b ^ (m - 1) * m := by
  have hc : ∀ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
      (bigDigits b n).length = m := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact length_bigDigits_eq hb hn.1 hn.2
  rw [Finset.sum_congr rfl hc, Finset.sum_const, card_mDigit hb m hm,
    smul_eq_mul]
end Champernowne
