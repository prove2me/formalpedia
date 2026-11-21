-- Prove2me | solution 1 for Champernowne.take_add_drop_countOccurrences_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:30.220968+00:00
-- url     : https://prove2.me/submissions/4b9a59ab-704b-43bd-b542-38719f37327f

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_add_countOccurrences_le_append


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {w : List ℕ} (hw : w ≠ [])
    (l : List ℕ) (n : ℕ) :
    countOccurrences w (l.take n) + countOccurrences w (l.drop n)
      ≤ countOccurrences w l := by
  conv_rhs => rw [← List.take_append_drop n l]
  exact add_countOccurrences_le_append hw ..
end Champernowne
