-- Prove2me | solution 1 for DeletionCode.SingleEditBubbles.LocalBubble.source_interval_in_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:46:45.785923+00:00
-- url     : https://prove2.me/submissions/b55254c1-a775-4356-be6e-31c4521cebbd

import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_SingleEditBubbles
import Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_negative_length_le_long
import Theorems.Thm_DeletionCode_RunBubbleConstruction_LocalBubble_long_end_le


set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditBubbles
open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation
open DeletionCode.SingleEditBubbles.LocalBubble
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}
namespace DeletionCode.SingleEditBubbles.LocalBubble
theorem _root_.solution (p : LocalBubble k source target pos orientation) :
    sourceInterval p ⊆ neighborhood (windowLength k) pos := by
  have hstart := p.edit_stop
  have hend := p.long_end_le
  have hnegative := negative_length_le_long p
  intro r hr
  have hrlow := hr.1
  have hrhigh := hr.2
  change pos - (windowLength k - 1) ≤ r ∧ r < pos + windowLength k + 1
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  constructor <;> omega
end DeletionCode.SingleEditBubbles.LocalBubble
