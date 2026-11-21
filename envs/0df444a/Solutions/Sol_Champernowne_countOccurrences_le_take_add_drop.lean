-- Prove2me | solution 1 for Champernowne.countOccurrences_le_take_add_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:35.419938+00:00
-- url     : https://prove2.me/submissions/555038ca-b4f0-4d55-9c72-19ae06a1757a

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_countOccurrences_append_le

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (w l : List ℕ) (n : ℕ) :
    countOccurrences w l
      ≤ countOccurrences w (l.take n) + countOccurrences w (l.drop n)
        + w.length := by
  conv_lhs => rw [← List.take_append_drop n l]
  exact countOccurrences_append_le ..
end Champernowne
