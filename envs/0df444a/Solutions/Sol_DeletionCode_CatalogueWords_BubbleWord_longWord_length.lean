-- Prove2me | solution 1 for DeletionCode.CatalogueWords.BubbleWord.longWord_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:20:21.578189+00:00
-- url     : https://prove2.me/submissions/f6da49b5-b8b5-4a98-a209-40b466d464ef

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
    bubble.longWord.length = longLength k bubble.header := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [longWord, List.length_append, List.length_replicate,
    bubble.left_length, bubble.right_length, longLength, header, windowLength]
  omega
end DeletionCode.CatalogueWords.BubbleWord
