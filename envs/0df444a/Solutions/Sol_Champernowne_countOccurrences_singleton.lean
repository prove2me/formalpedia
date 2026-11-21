-- Prove2me | solution 1 for Champernowne.countOccurrences_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:24.345561+00:00
-- url     : https://prove2.me/submissions/dee79ba2-80b0-460f-8d0c-d0c483acdbf7

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_countOccurrences_cons


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (d : ℕ) (l : List ℕ) :
    countOccurrences [d] l = l.count d := by
  induction l with
  | nil => simp [countOccurrences, List.isPrefixOf]
  | cons x xs ih =>
    rw [countOccurrences_cons, ih, List.count_cons]
    by_cases h : x = d
    · subst h
      simp [List.isPrefixOf]
    · have h' : ¬d = x := fun hdx => h hdx.symm
      simp [h, h', List.isPrefixOf]
end Champernowne
