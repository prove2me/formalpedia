-- Prove2me | solution 1 for DeletionCode.RunBubbleConstruction.LocalBubble.start_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:10.106899+00:00
-- url     : https://prove2.me/submissions/6596c164-60e1-403c-9788-6b964acda6a2

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction

set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
open DeletionCode.RunBubbleConstruction.LocalBubble
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}
namespace DeletionCode.RunBubbleConstruction.LocalBubble
theorem _root_.solution (p : LocalBubble k source target pos orientation) :
    p.before.length ≤ pos := by
  have h := p.edit_start
  omega
end DeletionCode.RunBubbleConstruction.LocalBubble
