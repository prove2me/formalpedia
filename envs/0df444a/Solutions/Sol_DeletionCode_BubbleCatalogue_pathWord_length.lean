-- Prove2me | solution 1 for DeletionCode.BubbleCatalogue.pathWord_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:41.860369+00:00
-- url     : https://prove2.me/submissions/cf414ffb-502a-4cc3-ac1c-503e6287868d

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_negativeWord_length
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_positiveWord_length


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators
namespace DeletionCode.BubbleCatalogue
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) (side : Bool) :
    (pathWord bubble side).length = PathMemory.pathLength k bubble.header side := by
  cases side <;> simp only [pathWord, PathMemory.pathLength, Bool.false_eq_true,
    ite_false, ite_true]
  · exact bubble.negativeWord_length
  · exact bubble.positiveWord_length
end DeletionCode.BubbleCatalogue
