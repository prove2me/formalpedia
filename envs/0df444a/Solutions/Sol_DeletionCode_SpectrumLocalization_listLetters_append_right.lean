-- Prove2me | solution 1 for DeletionCode.SpectrumLocalization.listLetters_append_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:22:59.047148+00:00
-- url     : https://prove2.me/submissions/b4280140-3564-4b92-9d17-6153086bd1e1

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators
namespace DeletionCode.SpectrumLocalization
theorem _root_.solution (x y : List Bool) (i : ℕ) :
    listLetters (x ++ y) (x.length + i) = listLetters y i := by
  simp only [listLetters, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
end DeletionCode.SpectrumLocalization
