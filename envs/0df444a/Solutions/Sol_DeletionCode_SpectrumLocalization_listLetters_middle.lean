-- Prove2me | solution 1 for DeletionCode.SpectrumLocalization.listLetters_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:26:24.80001+00:00
-- url     : https://prove2.me/submissions/eaaccf73-d6fc-43b1-bc22-bb0e45830817

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
import Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_append_left
import Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_append_right

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators
namespace DeletionCode.SpectrumLocalization
theorem _root_.solution (x p y : List Bool) (i : ℕ) (hi : i < p.length) :
    listLetters (x ++ (p ++ y)) (x.length + i) = listLetters p i := by
  rw [listLetters_append_right, listLetters_append_left p y i hi]
end DeletionCode.SpectrumLocalization
