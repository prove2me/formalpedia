-- Prove2me | solution 1 for DeletionCode.CatalogueWords.BubbleWord.positiveWord_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:04:41.204182+00:00
-- url     : https://prove2.me/submissions/8d549283-c140-46ff-88ff-c30804682447

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
    bubble.positiveWord.length = positiveLength k bubble.header := by
  cases ho : bubble.orientation <;>
    simp only [positiveWord, positiveLength, header, ho]
  · exact bubble.shortWord_length
  · exact bubble.longWord_length
end DeletionCode.CatalogueWords.BubbleWord
