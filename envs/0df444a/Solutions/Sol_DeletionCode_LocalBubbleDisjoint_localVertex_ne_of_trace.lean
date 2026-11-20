-- Prove2me | solution 1 for DeletionCode.LocalBubbleDisjoint.localVertex_ne_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:01:06.904906+00:00
-- url     : https://prove2.me/submissions/8efc0eff-d813-4d36-9219-b79f5bf2f520

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
import Theorems.Thm_DeletionCode_LocalBubbleDisjoint_localVertex_ne
import Theorems.Thm_DeletionCode_SingleEditBubbles_source_intervals_disjoint_of_trace


set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}
namespace DeletionCode.LocalBubbleDisjoint
theorem _root_.solution {trace : AlignmentTrace.Trace} (hk : 1 ≤ k)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : FiniteConflictGraph.Separated (4 * windowLength k) trace)
    (i j : Fin trace.length) (hi : FiniteConflictGraph.EditIndex trace i)
    (hj : FiniteConflictGraph.EditIndex trace j) (hne : i ≠ j)
    {target₁ target₂ : List Bool} {orientation₁ orientation₂ : Orientation}
    (p : LocalBubble k trace.source target₁ (trace.sourcePosition i.val) orientation₁)
    (q : LocalBubble k trace.source target₂ (trace.sourcePosition j.val) orientation₂)
    (side₁ side₂ : Bool) (a b : ℕ)
    (ha : a + (windowLength k - 1) ≤ (pathWord p side₁).length)
    (hb : b + (windowLength k - 1) ≤ (pathWord q side₂).length) :
    localVertex p side₁ a ≠ localVertex q side₂ b :=
  localVertex_ne hk hx p q
    (SingleEditBubbles.source_intervals_disjoint_of_trace hsep i j hi hj hne p q)
    side₁ side₂ a b ha hb
end DeletionCode.LocalBubbleDisjoint
