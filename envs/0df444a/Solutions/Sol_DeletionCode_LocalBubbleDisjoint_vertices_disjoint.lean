-- Prove2me | solution 1 for DeletionCode.LocalBubbleDisjoint.vertices_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:56:01.782009+00:00
-- url     : https://prove2.me/submissions/bfdb9e47-d1fb-4fd0-a0b4-00ddc53ecb48

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
import Theorems.Thm_DeletionCode_LocalBubbleDisjoint_source_bound
import Theorems.Thm_DeletionCode_LocalBubbleDisjoint_canonical_inside
import Theorems.Thm_DeletionCode_LocalBubbleDisjoint_canonical_valid
import Theorems.Thm_DeletionCode_LocalBubbleDisjoint_vertices_subset
import Theorems.Thm_DeletionCode_EditLocality_local_vertex_sets_disjoint
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_mono


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
    (hdis : Disjoint (SingleEditBubbles.LocalBubble.sourceInterval p)
      (SingleEditBubbles.LocalBubble.sourceInterval q)) (side₁ side₂ : Bool) :
    Disjoint (vertices p side₁) (vertices q side₂) := by
  exact (EditLocality.local_vertex_sets_disjoint hk (listLetters source) hx
    (canonicalEdit p side₁) (canonicalEdit q side₂)
    (canonical_valid p side₁) (canonical_valid q side₂)
    p.before.length p.bubble.negativeWord.length q.before.length q.bubble.negativeWord.length
    (canonical_inside p side₁) (canonical_inside q side₂)
    (source_bound p) (source_bound q) hdis).mono
      (vertices_subset p side₁) (vertices_subset q side₂)
end DeletionCode.LocalBubbleDisjoint
