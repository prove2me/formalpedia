-- Prove2me | solution 1 for DeletionCode.GeneratingBlocks.supplier_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:45.125039+00:00
-- url     : https://prove2.me/submissions/d4eaa70a-acda-4f7b-bdc5-63a3bf45c803

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks
import Theorems.Thm_DeletionCode_GeneratingBlocks_common_gram_adjacent

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph
namespace DeletionCode.GeneratingBlocks
theorem _root_.solution {I : Type*} {L : ℕ} (G : I → Gram L → ℤ)
    (i j : I) (g : Gram L) (hi : G i g = -1) (hj : G j g ≠ 0) :
    Connected G i j := by
  apply Relation.EqvGen.rel
  exact common_gram_adjacent G i j g (by omega) hj
end DeletionCode.GeneratingBlocks
