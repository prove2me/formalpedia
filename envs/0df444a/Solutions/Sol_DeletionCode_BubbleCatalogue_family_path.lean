-- Prove2me | solution 1 for DeletionCode.BubbleCatalogue.family_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:42.429092+00:00
-- url     : https://prove2.me/submissions/435ca744-6351-45ca-91e4-83fbc4c7ee88

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
import Theorems.Thm_DeletionCode_CatalogueWords_editedFamily_negative
import Theorems.Thm_DeletionCode_CatalogueWords_editedFamily_positive


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators
namespace DeletionCode.BubbleCatalogue
theorem _root_.solution {B : Type*} {k : ℕ} (words : B → BubbleWord k) (rank : B → ℕ)
    (b : B) (side : Bool) :
    (editedFamily words rank).family.path b side = listLetters (pathWord (words b) side) := by
  cases side
  · exact editedFamily_negative words rank b
  · exact editedFamily_positive words rank b
end DeletionCode.BubbleCatalogue
