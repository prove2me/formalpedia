-- Prove2me | solution 1 for DeletionCode.SingleEditBubbles.source_intervals_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:51:03.169061+00:00
-- url     : https://prove2.me/submissions/39b14a55-0f73-42cf-a014-240a23f8ad5a

import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_SingleEditBubbles
import Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_source_interval_in_neighborhood
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_mono
import Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_disjoint_of_gap


set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditBubbles
open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation
namespace DeletionCode.SingleEditBubbles
theorem _root_.solution {k a b : ℕ} {source target₁ target₂ : List Bool}
    {orientation₁ orientation₂ : Orientation}
    (p : RunBubbleConstruction.LocalBubble k source target₁ a orientation₁)
    (q : RunBubbleConstruction.LocalBubble k source target₂ b orientation₂)
    (hgap : a + 4 * windowLength k ≤ b) :
    Disjoint (LocalBubble.sourceInterval p) (LocalBubble.sourceInterval q) :=
  (neighborhood_disjoint_of_gap (by unfold windowLength; omega) hgap).mono
    (LocalBubble.source_interval_in_neighborhood p) (LocalBubble.source_interval_in_neighborhood q)
end DeletionCode.SingleEditBubbles
