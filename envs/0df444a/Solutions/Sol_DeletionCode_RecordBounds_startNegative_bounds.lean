-- Prove2me | solution 1 for DeletionCode.RecordBounds.startNegative_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:01:27.847738+00:00
-- url     : https://prove2.me/submissions/b8e87332-9af4-46f0-a1c7-6556a9038b89

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
import Theorems.Thm_DeletionCode_RecordBounds_writeBits_bounds

set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
namespace DeletionCode.RecordBounds
theorem _root_.solution (k : ℕ) (h : Header) (offset : ℕ) (bits : PartialWords.Bits k)
    (s t : Memory) (hs : ConcreteStart.startNegative k h offset bits s = some t) :
    offset + k ≤ negativeLength k h :=
  writeBits_bounds s t (negativeLength k h) offset k bits hs
end DeletionCode.RecordBounds
