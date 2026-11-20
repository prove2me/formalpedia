-- Prove2me | solution 1 for DeletionCode.UniqueWordCount.half_words_le_card_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:00:38.096576+00:00
-- url     : https://prove2.me/submissions/fda962f6-f2bc-4ae9-82c1-058932abbd04

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_OverlapCollision
import Definitions.Def_DeletionCode_FinitePairUnion
import Definitions.Def_DeletionCode_UniqueWordParameters
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_DeletionCode_UniqueWordCount
import Theorems.Thm_DeletionCode_UniqueWordCount_most_words_unique
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans


set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordCount
open Windows HeaderRecovery
attribute [local instance] Classical.propDecidable
namespace DeletionCode.UniqueWordCount
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n - 1) ≤ (uniqueWords n (UniqueWordParameters.uniquenessLength n)).card := by
  obtain ⟨hcount, hfrac, hhalf⟩ := most_words_unique n hn
  exact_mod_cast hhalf.trans (hfrac.trans hcount)
end DeletionCode.UniqueWordCount
