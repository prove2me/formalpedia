-- Prove2me | solution 1 for DeletionCode.CatalogueWords.BubbleWord.shortWord_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:20:23.623375+00:00
-- url     : https://prove2.me/submissions/45d38cc2-92ad-4e23-bffe-553751b23057

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
    bubble.shortWord.length = shortLength k bubble.header := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [shortWord, List.length_append, List.length_replicate,
    bubble.left_length, bubble.right_length, shortLength, longLength, header, windowLength]
  omega
end DeletionCode.CatalogueWords.BubbleWord
