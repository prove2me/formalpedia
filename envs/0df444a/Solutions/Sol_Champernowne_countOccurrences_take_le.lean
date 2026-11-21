-- Prove2me | solution 1 for Champernowne.countOccurrences_take_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:18.897478+00:00
-- url     : https://prove2.me/submissions/ee801d8c-e3f2-4567-ba0a-33076529825b

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_countOccurrences_le_append_right

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (w l : List ℕ) (n : ℕ) :
    countOccurrences w (l.take n) ≤ countOccurrences w l := by
  conv_rhs => rw [← List.take_append_drop n l]
  exact countOccurrences_le_append_right ..
end Champernowne
