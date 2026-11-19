-- Prove2me | solution 1 for DeletionCode.CatalogueWords.BubbleWord.negativeWord_semantics
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:26:25.594614+00:00
-- url     : https://prove2.me/submissions/f135afe7-67fe-44db-9d66-8a6a544f01e8

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_delete_longWord

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}
namespace DeletionCode.CatalogueWords.BubbleWord
theorem _root_.solution (bubble : BubbleWord k) :
    listLetters bubble.negativeWord =
      negativePath k bubble.header (listLetters bubble.longWord) := by
  cases ho : bubble.orientation <;>
    simp only [negativeWord, negativePath, header, ho]
  exact bubble.delete_longWord.symm
end DeletionCode.CatalogueWords.BubbleWord
