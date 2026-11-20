-- Prove2me | solution 1 for DeletionCode.GeneratingBlocks.blockHull_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:08:35.724895+00:00
-- url     : https://prove2.me/submissions/19cd6b55-b7bd-410b-9dda-2c519617e0b8

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph
namespace DeletionCode.GeneratingBlocks
theorem _root_.solution {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) (T : Set I) :
    BlockClosed G (blockHull G T) := by
  rintro i ⟨a, ha, hai⟩ j hij
  exact ⟨a, ha, Relation.EqvGen.trans a i j hai hij⟩
end DeletionCode.GeneratingBlocks
