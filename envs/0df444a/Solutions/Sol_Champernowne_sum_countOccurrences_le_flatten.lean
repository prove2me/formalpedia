-- Prove2me | solution 1 for Champernowne.sum_countOccurrences_le_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:25.97772+00:00
-- url     : https://prove2.me/submissions/dc8e7e06-129f-43eb-907b-902a2e72ddfd

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_add_countOccurrences_le_append
public import Theorems.Thm_Champernowne_countOccurrences_nil


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {w : List ℕ} (hw : w ≠ [])
    (L : List (List ℕ)) :
    (L.map (countOccurrences w)).sum ≤ countOccurrences w L.flatten := by
  induction L with
  | nil => simp [countOccurrences_nil hw]
  | cons l L' ih =>
    rw [List.flatten_cons, List.map_cons, List.sum_cons]
    calc countOccurrences w l + (L'.map (countOccurrences w)).sum
        ≤ countOccurrences w l + countOccurrences w L'.flatten :=
          Nat.add_le_add_left ih _
    _ ≤ countOccurrences w (l ++ L'.flatten) :=
          add_countOccurrences_le_append hw _ _
end Champernowne
