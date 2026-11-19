-- Prove2me | solution 1 for DeletionCode.SingleEditScripts.eraseIdx_at_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:29:24.097374+00:00
-- url     : https://prove2.me/submissions/e4e8c002-fc18-40a6-9545-f71aeca95e29

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts

set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditScripts
open Windows CatalogueWords EditAlignment SingleEditOrigins
namespace DeletionCode.SingleEditScripts
theorem _root_.solution (pre suffix : List Bool) (bit : Bool) :
    (pre ++ bit :: suffix).eraseIdx pre.length = pre ++ suffix := by
  rw [List.eraseIdx_append_of_length_le (Nat.le_refl _)]
  simp
end DeletionCode.SingleEditScripts
