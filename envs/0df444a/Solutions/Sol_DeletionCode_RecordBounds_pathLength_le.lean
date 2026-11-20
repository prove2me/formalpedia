-- Prove2me | solution 1 for DeletionCode.RecordBounds.pathLength_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:00:40.284153+00:00
-- url     : https://prove2.me/submissions/afff9fbb-8598-45c2-93e4-80c1946e480f

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds

set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
namespace DeletionCode.RecordBounds
theorem _root_.solution (k : ℕ) (h : Header) (side : Bool) :
    pathLength k h side ≤ 2 * windowLength k := by
  cases side <;> cases ho : h.orientation <;>
    simp [pathLength, negativeLength, positiveLength, shortLength, longLength, ho] <;> omega
end DeletionCode.RecordBounds
