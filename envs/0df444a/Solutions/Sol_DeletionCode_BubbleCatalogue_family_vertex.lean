-- Prove2me | solution 1 for DeletionCode.BubbleCatalogue.family_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:58.258274+00:00
-- url     : https://prove2.me/submissions/50199dc9-337d-4c07-ad71-f9e9789266cc

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
import Theorems.Thm_DeletionCode_BubbleCatalogue_family_path

set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators
namespace DeletionCode.BubbleCatalogue
theorem _root_.solution {B : Type*} {k : ℕ} (words : B → BubbleWord k) (rank : B → ℕ)
    (b : B) (side : Bool) (i : ℕ) :
    SupportComponents.vertex (editedFamily words rank).family (windowLength k) b side i =
      SpectrumPath.vertexAt (listLetters (pathWord (words b) side)) (windowLength k) i := by
  funext j
  exact congrFun (family_path words rank b side) (i + j.val)
end DeletionCode.BubbleCatalogue
