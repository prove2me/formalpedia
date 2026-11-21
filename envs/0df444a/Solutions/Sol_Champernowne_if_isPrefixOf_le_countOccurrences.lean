-- Prove2me | solution 1 for Champernowne.if_isPrefixOf_le_countOccurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:54.616864+00:00
-- url     : https://prove2.me/submissions/45c6d149-c134-45b7-a50c-b62d059775da

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_countOccurrences_cons
public import Theorems.Thm_P2M_Champernowne_countOccurrences_nil__4d47a4d3551b


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (w l : List ℕ) :
    (if w.isPrefixOf l then 1 else 0) ≤ countOccurrences w l := by
  rcases l with _ | ⟨x, xs⟩
  · rw [countOccurrences_nil']
  · rw [countOccurrences_cons]
    omega
end Champernowne
