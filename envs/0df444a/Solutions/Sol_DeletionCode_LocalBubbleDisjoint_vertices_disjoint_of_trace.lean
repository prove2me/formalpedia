-- Prove2me | solution 1 for DeletionCode.LocalBubbleDisjoint.vertices_disjoint_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:00:47.994828+00:00
-- url     : https://prove2.me/submissions/804ddd14-73be-4d7f-a71f-1f400beaba99

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
import Theorems.Thm_DeletionCode_LocalBubbleDisjoint_vertices_disjoint
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
    (side₁ side₂ : Bool) : Disjoint (vertices p side₁) (vertices q side₂) :=
  vertices_disjoint hk hx p q
    (SingleEditBubbles.source_intervals_disjoint_of_trace hsep i j hi hj hne p q) side₁ side₂
end DeletionCode.LocalBubbleDisjoint
