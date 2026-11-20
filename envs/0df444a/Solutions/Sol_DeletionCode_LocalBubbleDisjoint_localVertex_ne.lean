-- Prove2me | solution 1 for DeletionCode.LocalBubbleDisjoint.localVertex_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:59:12.232267+00:00
-- url     : https://prove2.me/submissions/0c5a7d86-a071-4c51-97ef-7cf013542193

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
import Theorems.Thm_DeletionCode_LocalBubbleDisjoint_vertices_disjoint
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm


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
      (SingleEditBubbles.LocalBubble.sourceInterval q)) (side₁ side₂ : Bool) (i j : ℕ)
    (hi : i + (windowLength k - 1) ≤ (pathWord p side₁).length)
    (hj : j + (windowLength k - 1) ≤ (pathWord q side₂).length) :
    localVertex p side₁ i ≠ localVertex q side₂ j := by
  intro heq
  exact Set.disjoint_left.mp (vertices_disjoint hk hx p q hdis side₁ side₂)
    ⟨i, hi, rfl⟩ ⟨j, hj, heq.symm⟩
end DeletionCode.LocalBubbleDisjoint
