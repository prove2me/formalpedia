-- Prove2me | solution 1 for DeletionCode.CatalogueWords.listLetters_eraseIdx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:20:04.824891+00:00
-- url     : https://prove2.me/submissions/77f34ce8-f68e-4f48-a6b6-a382e9c8912f

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
namespace DeletionCode.CatalogueWords
theorem _root_.solution (word : List Bool) (ell : ℕ) :
    listLetters (word.eraseIdx ell) = deleteAt (listLetters word) ell := by
  funext i
  simp only [listLetters, deleteAt, List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  by_cases hi : i < ell <;> simp only [hi, ite_true, ite_false]
end DeletionCode.CatalogueWords
