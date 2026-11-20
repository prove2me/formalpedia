-- Prove2me | solution 1 for DeletionCode.LocalBubbleDisjoint.vertices_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:52:29.684607+00:00
-- url     : https://prove2.me/submissions/8e51f4f7-4e65-437a-81d9-a1ae234b3ccf

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
import Theorems.Thm_DeletionCode_LocalBubbleDisjoint_localVertex_mem

set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}
namespace DeletionCode.LocalBubbleDisjoint
theorem _root_.solution (p : LocalBubble k source target pos orientation) (side : Bool) :
    vertices p side ⊆ EditLocality.localVertices (canonicalEdit p side)
      (listLetters source) p.before.length p.bubble.negativeWord.length (windowLength k) := by
  rintro v ⟨offset, hbound, rfl⟩
  exact localVertex_mem p side offset hbound
end DeletionCode.LocalBubbleDisjoint
