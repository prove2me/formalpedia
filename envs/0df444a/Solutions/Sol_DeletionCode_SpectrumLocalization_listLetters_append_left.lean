-- Prove2me | solution 1 for DeletionCode.SpectrumLocalization.listLetters_append_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:25:40.63843+00:00
-- url     : https://prove2.me/submissions/fc308472-2eda-41b5-bb62-173a7512e6c3

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators
namespace DeletionCode.SpectrumLocalization
theorem _root_.solution (x y : List Bool) (i : ℕ) (hi : i < x.length) :
    listLetters (x ++ y) i = listLetters x i := by
  simp only [listLetters, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hi]
end DeletionCode.SpectrumLocalization
