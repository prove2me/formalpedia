-- Prove2me | solution 1 for Champernowne.countOccurrences_drop_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:00.319213+00:00
-- url     : https://prove2.me/submissions/acc0c0c1-4be2-461f-b7a8-2aa00fe7b4ea

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_countOccurrences_le_append_left

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (w l : List ℕ) (n : ℕ) :
    countOccurrences w (l.drop n) ≤ countOccurrences w l := by
  conv_rhs => rw [← List.take_append_drop n l]
  exact countOccurrences_le_append_left ..
end Champernowne
