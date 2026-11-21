-- Prove2me | solution 1 for Champernowne.countOccurrences_eq_zero_of_length_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:38.46495+00:00
-- url     : https://prove2.me/submissions/697f4c0f-ffe4-45a7-8caa-923d1f1d879d

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_countOccurrences_eq_card_filter_range


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {w l : List ℕ}
    (h : l.length < w.length) : countOccurrences w l = 0 := by
  rw [countOccurrences_eq_card_filter_range, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro j hj
  rw [Finset.mem_range] at hj
  intro hpre
  have hle := (List.isPrefixOf_iff_prefix.mp hpre).length_le
  rw [List.length_drop] at hle
  omega
end Champernowne
