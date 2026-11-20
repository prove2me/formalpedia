-- Prove2me | solution 1 for DeletionCode.BubblePathSimplicity.local_word_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:40.403334+00:00
-- url     : https://prove2.me/submissions/eb4d036a-1665-4516-8114-c8cd80acdd1c

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Theorems.Thm_DeletionCode_BubblePathSimplicity_substring_unique
import Theorems.Thm_DeletionCode_EditRigidity_one_edit_unique


set_option autoImplicit true
open DeletionCode DeletionCode.BubblePathSimplicity
open Windows HeaderRecovery CatalogueWords SingleEditOrigins
namespace DeletionCode.BubblePathSimplicity
theorem _root_.solution {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e : Edit) (he : e.Valid n)
    (word : List Bool) (s : ℕ)
    (hbound : s + word.length ≤ e.outputLength n)
    (hocc : Agree (listLetters word) 0 (e.word x) s word.length) :
    KUnique (listLetters word) word.length (windowLength k - 1) :=
  substring_unique (e.word x) (listLetters word) (e.outputLength n) word.length
    (windowLength k - 1) s (EditRigidity.one_edit_unique hk x hx e he) hbound hocc
end DeletionCode.BubblePathSimplicity
