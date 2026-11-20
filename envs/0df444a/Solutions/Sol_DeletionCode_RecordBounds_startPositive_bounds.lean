-- Prove2me | solution 1 for DeletionCode.RecordBounds.startPositive_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:00:56.002594+00:00
-- url     : https://prove2.me/submissions/f7f788d6-b71e-424e-8a52-f56aae0838a4

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds

set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
namespace DeletionCode.RecordBounds
theorem _root_.solution (k : ℕ) (h : Header) (offset : ℕ) (bits : PartialWords.Bits k)
    (extra : Bool) (s t : Memory)
    (hs : ConcreteStart.startPositive k h offset bits extra s = some t) :
    offset + k ≤ positiveLength k h := by
  unfold ConcreteStart.startPositive at hs
  split at hs
  · assumption
  · contradiction
end DeletionCode.RecordBounds
