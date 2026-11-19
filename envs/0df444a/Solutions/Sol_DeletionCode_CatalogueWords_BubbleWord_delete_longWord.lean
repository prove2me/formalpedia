-- Prove2me | solution 1 for DeletionCode.CatalogueWords.BubbleWord.delete_longWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:25:14.311899+00:00
-- url     : https://prove2.me/submissions/89b0e020-2a3e-4e6a-ab30-743ebf5e1cc8

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
import Theorems.Thm_DeletionCode_CatalogueWords_listLetters_eraseIdx
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_eraseIdx_longWord

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}
namespace DeletionCode.CatalogueWords.BubbleWord
theorem _root_.solution (bubble : BubbleWord k) :
    deleteAt (listLetters bubble.longWord) (editOffset k) = listLetters bubble.shortWord := by
  rw [← listLetters_eraseIdx, bubble.eraseIdx_longWord]
end DeletionCode.CatalogueWords.BubbleWord
