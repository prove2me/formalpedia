-- Prove2me | solution 1 for DeletionCode.RunBubbleConstruction.LocalBubble.long_interval_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:10.562251+00:00
-- url     : https://prove2.me/submissions/c665ae0b-25c1-42c8-b47f-45d5235d0ab9

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction
import Theorems.Thm_DeletionCode_RunBubbleConstruction_LocalBubble_long_end_le

set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
open DeletionCode.RunBubbleConstruction.LocalBubble
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}
namespace DeletionCode.RunBubbleConstruction.LocalBubble
theorem _root_.solution (p : LocalBubble k source target pos orientation) :
    pos + 1 - windowLength k ≤ p.before.length ∧
      p.before.length + p.bubble.longWord.length ≤ pos + windowLength k := by
  constructor
  · have h := p.edit_stop
    omega
  · exact p.long_end_le
end DeletionCode.RunBubbleConstruction.LocalBubble
