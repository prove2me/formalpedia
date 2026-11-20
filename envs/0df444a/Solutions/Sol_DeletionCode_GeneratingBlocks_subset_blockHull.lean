-- Prove2me | solution 1 for DeletionCode.GeneratingBlocks.subset_blockHull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:09:38.856482+00:00
-- url     : https://prove2.me/submissions/e4f856f1-1004-413c-869f-d9b25c61014c

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph
namespace DeletionCode.GeneratingBlocks
theorem _root_.solution {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) (T : Set I) :
    T ⊆ blockHull G T := by
  intro i hi
  exact ⟨i, hi, Relation.EqvGen.refl i⟩
end DeletionCode.GeneratingBlocks
