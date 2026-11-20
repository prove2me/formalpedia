-- Prove2me | solution 1 for DeletionCode.RecordBounds.writeBits_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:00:51.785337+00:00
-- url     : https://prove2.me/submissions/11dc5d86-c316-4786-8cee-9f8f54659817

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds

set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
namespace DeletionCode.RecordBounds
theorem _root_.solution (s t : Memory) (m start len : ℕ) (bits : PartialWords.Bits len)
    (h : writeBits s m start bits = some t) : start + len ≤ m := by
  unfold writeBits at h
  split at h
  · rename_i hb
    exact hb.1
  · contradiction
end DeletionCode.RecordBounds
