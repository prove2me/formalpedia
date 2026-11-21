-- Prove2me | solution 1 for Champernowne.countOccurrences_le_append_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:21.197927+00:00
-- url     : https://prove2.me/submissions/d3aa7d9e-220f-4703-a752-6b75735863e9

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_countOccurrences_le_cons

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (w a b : List ℕ) :
    countOccurrences w b ≤ countOccurrences w (a ++ b) := by
  induction a with
  | nil => simp
  | cons x a' ih =>
    rw [List.cons_append]
    exact ih.trans (countOccurrences_le_cons w _ x)
end Champernowne
