-- Prove2me | solution 1 for DeletionCode.CatalogueWords.BubbleWord.negativeWord_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:04:07.09143+00:00
-- url     : https://prove2.me/submissions/5a7795b9-b7ea-47bf-9ed9-bc10515fa91b

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_longWord_length
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_shortWord_length

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}
namespace DeletionCode.CatalogueWords.BubbleWord
theorem _root_.solution (bubble : BubbleWord k) :
    bubble.negativeWord.length = negativeLength k bubble.header := by
  cases ho : bubble.orientation <;>
    simp only [negativeWord, negativeLength, header, ho]
  · exact bubble.longWord_length
  · exact bubble.shortWord_length
end DeletionCode.CatalogueWords.BubbleWord
