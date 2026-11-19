-- Prove2me | solution 1 for DeletionCode.SingleEditScripts.listLetters_at_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:29:27.804488+00:00
-- url     : https://prove2.me/submissions/d0ea6377-7b39-4eac-ad3a-083ebde345f8

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts

set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditScripts
open Windows CatalogueWords EditAlignment SingleEditOrigins
namespace DeletionCode.SingleEditScripts
theorem _root_.solution (pre suffix : List Bool) (bit : Bool) :
    listLetters (pre ++ bit :: suffix) pre.length = bit := by
  simp only [listLetters, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp
end DeletionCode.SingleEditScripts
