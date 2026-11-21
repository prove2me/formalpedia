-- Prove2me | solution 1 for Champernowne.countOccurrences_append_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:59.800919+00:00
-- url     : https://prove2.me/submissions/07f8c5a7-10eb-4c39-ac23-a1fd7be9d46e

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_countOccurrences_append_le_min

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (w a b : List ℕ) :
    countOccurrences w (a ++ b)
      ≤ countOccurrences w a + countOccurrences w b + w.length :=
  (countOccurrences_append_le_min w a b).trans
    (Nat.add_le_add_left (Nat.min_le_left _ _) _)
end Champernowne
