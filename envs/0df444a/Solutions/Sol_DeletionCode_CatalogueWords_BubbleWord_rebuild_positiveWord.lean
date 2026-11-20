-- Prove2me | solution 1 for DeletionCode.CatalogueWords.BubbleWord.rebuild_positiveWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:52.429958+00:00
-- url     : https://prove2.me/submissions/fe186cd5-2e9a-48d2-898d-a25884311f16

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_negativeWord_semantics
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_positiveWord_semantics
import Theorems.Thm_DeletionCode_HeaderRecovery_rebuild_positive_correct


set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}
namespace DeletionCode.CatalogueWords.BubbleWord
theorem _root_.solution (bubble : BubbleWord k) :
    rebuildPositive k bubble.header (listLetters bubble.negativeWord) =
      listLetters bubble.positiveWord := by
  rw [bubble.negativeWord_semantics, bubble.positiveWord_semantics]
  exact rebuild_positive_correct k bubble.header (listLetters bubble.longWord) bubble.header_bit
end DeletionCode.CatalogueWords.BubbleWord
