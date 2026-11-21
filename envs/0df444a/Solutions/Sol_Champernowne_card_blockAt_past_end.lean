-- Prove2me | solution 1 for Champernowne.card_blockAt_past_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:14.621374+00:00
-- url     : https://prove2.me/submissions/fa9f76e0-d3fc-47a6-9dc1-e238971153e3

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_length_bigDigits_eq


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (m j : ℕ) {w : List ℕ}
    (hwne : w ≠ []) (hj : m < j + w.length) :
    ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn
  rw [Finset.mem_Ico] at hn
  have hlen := length_bigDigits_eq hb hn.1 hn.2
  intro heq
  have hlw := congrArg List.length heq
  rw [List.length_take, List.length_drop, hlen] at hlw
  have hkpos := List.length_pos_of_ne_nil hwne
  omega
end Champernowne
