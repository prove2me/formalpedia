-- Prove2me | solution 1 for DeletionCode.CatalogueWords.editedFamily_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:05:42.994964+00:00
-- url     : https://prove2.me/submissions/05ba1cbc-ffeb-49e8-b3a7-63ea01debd05

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_positiveWord_semantics

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
namespace DeletionCode.CatalogueWords
theorem _root_.solution {B : Type*} {k : ℕ}
    (bubbles : B → BubbleWord k) (rank : B → ℕ) (b : B) :
    (editedFamily bubbles rank).family.path b true = listLetters (bubbles b).positiveWord :=
  (bubbles b).positiveWord_semantics.symm
end DeletionCode.CatalogueWords
