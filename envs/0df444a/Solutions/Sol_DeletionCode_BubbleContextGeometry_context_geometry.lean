-- Prove2me | solution 1 for DeletionCode.BubbleContextGeometry.context_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:50.133255+00:00
-- url     : https://prove2.me/submissions/2c72853c-b298-45be-85a6-230d0badf3c9

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Theorems.Thm_DeletionCode_BubbleContextGeometry_deletion_geometry
import Theorems.Thm_DeletionCode_BubbleContextGeometry_insertion_geometry

set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization
namespace DeletionCode.BubbleContextGeometry
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit)) (x y : List Bool)
    (hx : KUnique (listLetters (x ++ (bubble.negativeWord ++ y)))
      (x ++ (bubble.negativeWord ++ y)).length k) : Geometry bubble := by
  cases ho : bubble.orientation with
  | deletion =>
    simp only [BubbleWord.negativeWord, ho] at hx
    exact deletion_geometry hk bubble hleft hright x y hx
  | insertion =>
    simp only [BubbleWord.negativeWord, ho] at hx
    exact insertion_geometry hk bubble hleft hright x y hx
end DeletionCode.BubbleContextGeometry
