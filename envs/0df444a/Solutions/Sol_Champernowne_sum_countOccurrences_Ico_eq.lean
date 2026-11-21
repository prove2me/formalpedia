-- Prove2me | solution 1 for Champernowne.sum_countOccurrences_Ico_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:35.022176+00:00
-- url     : https://prove2.me/submissions/0009dae1-479b-4bf4-b9af-0f33e08841aa

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Theorems.Thm_Champernowne_length_bigDigits_eq
public import Theorems.Thm_Champernowne_countOccurrences_eq_card_filter_range


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (K t : ℕ) (w : List ℕ)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
      = ∑ j ∈ Finset.range (K + 2),
          ((Finset.Ico (b ^ K) (b ^ K + t)).filter
            (fun n => ((bigDigits b n).drop j).take w.length = w)).card := by
  have hstep : ∀ n ∈ Finset.Ico (b ^ K) (b ^ K + t),
      countOccurrences w (bigDigits b n)
        = ∑ j ∈ Finset.range (K + 2),
            if ((bigDigits b n).drop j).take w.length = w then 1 else 0 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hpred : ∀ j ∈ Finset.range (K + 2),
        (w.isPrefixOf ((bigDigits b n).drop j) = true)
          ↔ ((bigDigits b n).drop j).take w.length = w := fun j _ => by
      rw [List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take, eq_comm]
    rw [countOccurrences_eq_card_filter_range,
      length_bigDigits_eq (m := K + 1) hb hn.1 (by omega), Finset.filter_congr hpred,
      Finset.card_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm
end Champernowne
