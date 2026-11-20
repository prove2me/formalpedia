-- Prove2me | solution 1 for DeletionCode.CatalogueWords.editedFamily_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:04:56.420334+00:00
-- url     : https://prove2.me/submissions/2be7e700-40e2-453e-90a5-86c2985afe1c

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_negativeWord_semantics

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
namespace DeletionCode.CatalogueWords
theorem _root_.solution {B : Type*} {k : ℕ}
    (bubbles : B → BubbleWord k) (rank : B → ℕ) (b : B) :
    (editedFamily bubbles rank).family.path b false = listLetters (bubbles b).negativeWord :=
  (bubbles b).negativeWord_semantics.symm
end DeletionCode.CatalogueWords
