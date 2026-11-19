-- Prove2me | solution 1 for DeletionCode.CatalogueWords.BubbleWord.positiveWord_semantics
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:26:26.442221+00:00
-- url     : https://prove2.me/submissions/dd469993-14e7-4146-8449-55111d8968dc

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
    listLetters bubble.positiveWord =
      positivePath k bubble.header (listLetters bubble.longWord) := by
  cases ho : bubble.orientation <;>
    simp only [positiveWord, positivePath, header, ho]
  exact bubble.delete_longWord.symm
end DeletionCode.CatalogueWords.BubbleWord
