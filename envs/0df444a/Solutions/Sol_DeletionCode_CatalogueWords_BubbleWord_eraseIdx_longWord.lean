-- Prove2me | solution 1 for DeletionCode.CatalogueWords.BubbleWord.eraseIdx_longWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:24:34.435208+00:00
-- url     : https://prove2.me/submissions/7fe59962-72aa-4c5b-9560-5d8e8c2d1051

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}
namespace DeletionCode.CatalogueWords.BubbleWord
theorem _root_.solution (bubble : BubbleWord k) :
    bubble.longWord.eraseIdx (editOffset k) = bubble.shortWord := by
  have hleft := bubble.edit_in_run.1
  have hrun := bubble.edit_in_run.2
  unfold longWord shortWord
  rw [List.eraseIdx_append_of_length_le hleft]
  rw [List.eraseIdx_append_of_lt_length
    (by simpa only [List.length_replicate] using hrun)]
  rw [List.eraseIdx_replicate, if_pos hrun]
end DeletionCode.CatalogueWords.BubbleWord
