-- Prove2me | solution 1 for DeletionCode.BubbleCatalogue.pathWord_length_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:56.940395+00:00
-- url     : https://prove2.me/submissions/87ec32c2-4c16-4654-a752-34a3183e9611

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
import Theorems.Thm_DeletionCode_BubbleCatalogue_pathWord_length

set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators
namespace DeletionCode.BubbleCatalogue
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) (side : Bool) :
    windowLength k ≤ (pathWord bubble side).length := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  rw [pathWord_length]
  cases side <;> cases ho : bubble.orientation <;>
    simp only [PathMemory.pathLength, negativeLength, positiveLength, longLength,
      shortLength, BubbleWord.header, ho, Bool.false_eq_true, ite_false, ite_true, windowLength] <;>
    omega
end DeletionCode.BubbleCatalogue
