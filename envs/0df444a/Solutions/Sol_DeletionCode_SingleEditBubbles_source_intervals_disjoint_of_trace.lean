-- Prove2me | solution 1 for DeletionCode.SingleEditBubbles.source_intervals_disjoint_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:58:26.881021+00:00
-- url     : https://prove2.me/submissions/aef6a38a-d23f-4a9b-b437-69f7da83ef49

import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_SingleEditBubbles
import Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_source_interval_in_neighborhood
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_mono
import Theorems.Thm_DeletionCode_TraceSeparation_source_neighborhood_disjoint


set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditBubbles
open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation
namespace DeletionCode.SingleEditBubbles
theorem _root_.solution {k : ℕ} {trace : AlignmentTrace.Trace}
    (hsep : FiniteConflictGraph.Separated (4 * windowLength k) trace)
    (i j : Fin trace.length) (hi : FiniteConflictGraph.EditIndex trace i)
    (hj : FiniteConflictGraph.EditIndex trace j) (hne : i ≠ j)
    {target₁ target₂ : List Bool} {orientation₁ orientation₂ : Orientation}
    (p : RunBubbleConstruction.LocalBubble k trace.source target₁ (trace.sourcePosition i.val) orientation₁)
    (q : RunBubbleConstruction.LocalBubble k trace.source target₂ (trace.sourcePosition j.val) orientation₂) :
    Disjoint (LocalBubble.sourceInterval p) (LocalBubble.sourceInterval q) :=
  (source_neighborhood_disjoint (by unfold windowLength; omega) hsep i j hi hj hne).mono
    (LocalBubble.source_interval_in_neighborhood p) (LocalBubble.source_interval_in_neighborhood q)
end DeletionCode.SingleEditBubbles
