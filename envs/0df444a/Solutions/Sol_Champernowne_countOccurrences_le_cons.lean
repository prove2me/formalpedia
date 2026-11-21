-- Prove2me | solution 1 for Champernowne.countOccurrences_le_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:44.235924+00:00
-- url     : https://prove2.me/submissions/37c44e96-264b-4565-a119-3656b91526b8

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
theorem _root_.solution (w l : List ℕ) (x : ℕ) :
    countOccurrences w l ≤ countOccurrences w (x :: l) := by
  rw [countOccurrences_cons]
  omega
end Champernowne
