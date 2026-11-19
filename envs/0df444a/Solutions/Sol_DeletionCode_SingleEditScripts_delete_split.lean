-- Prove2me | solution 1 for DeletionCode.SingleEditScripts.delete_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:30:27.500207+00:00
-- url     : https://prove2.me/submissions/1f5e6b71-20af-40e4-a708-53953029a549

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts
import Theorems.Thm_DeletionCode_SingleEditScripts_eraseIdx_at_split
import Theorems.Thm_DeletionCode_CatalogueWords_listLetters_eraseIdx


set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditScripts
open Windows CatalogueWords EditAlignment SingleEditOrigins
namespace DeletionCode.SingleEditScripts
theorem _root_.solution (pre suffix : List Bool) (bit : Bool) :
    deleteAt (listLetters (pre ++ bit :: suffix)) pre.length =
      listLetters (pre ++ suffix) := by
  rw [← listLetters_eraseIdx, eraseIdx_at_split]
end DeletionCode.SingleEditScripts
