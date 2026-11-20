-- Prove2me | solution 1 for DeletionCode.LocalBubbleDisjoint.vertices_disjoint_of_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:59:12.86661+00:00
-- url     : https://prove2.me/submissions/132cfb70-9453-4c29-a8f4-89b03611def2

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
import Theorems.Thm_DeletionCode_LocalBubbleDisjoint_vertices_disjoint
import Theorems.Thm_DeletionCode_SingleEditBubbles_source_intervals_disjoint


set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}
namespace DeletionCode.LocalBubbleDisjoint
theorem _root_.solution {a b : ℕ} {target₁ target₂ : List Bool}
    {orientation₁ orientation₂ : Orientation} (hk : 1 ≤ k)
    (hx : KUnique (listLetters source) source.length k)
    (p : LocalBubble k source target₁ a orientation₁)
    (q : LocalBubble k source target₂ b orientation₂)
    (hgap : a + 4 * windowLength k ≤ b) (side₁ side₂ : Bool) :
    Disjoint (vertices p side₁) (vertices q side₂) :=
  vertices_disjoint hk hx p q (SingleEditBubbles.source_intervals_disjoint p q hgap) side₁ side₂
end DeletionCode.LocalBubbleDisjoint
