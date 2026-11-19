-- Prove2me | solution 1 for DeletionCode.SingleEditScripts.insert_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:32:55.471568+00:00
-- url     : https://prove2.me/submissions/e6c32c62-917a-4c41-8c27-a1251a21a372

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts
import Theorems.Thm_DeletionCode_SingleEditScripts_listLetters_at_split
import Theorems.Thm_DeletionCode_SingleEditScripts_delete_split
import Theorems.Thm_DeletionCode_Windows_insert_delete


set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditScripts
open Windows CatalogueWords EditAlignment SingleEditOrigins
namespace DeletionCode.SingleEditScripts
theorem _root_.solution (pre suffix : List Bool) (bit : Bool) :
    insertAt (listLetters (pre ++ suffix)) pre.length bit =
      listLetters (pre ++ bit :: suffix) := by
  have hdel := delete_split pre suffix bit
  have hbit := listLetters_at_split pre suffix bit
  calc
    insertAt (listLetters (pre ++ suffix)) pre.length bit =
        insertAt (deleteAt (listLetters (pre ++ bit :: suffix)) pre.length)
          pre.length (listLetters (pre ++ bit :: suffix) pre.length) := by
      rw [hdel, hbit]
    _ = listLetters (pre ++ bit :: suffix) := insert_delete _ _
end DeletionCode.SingleEditScripts
