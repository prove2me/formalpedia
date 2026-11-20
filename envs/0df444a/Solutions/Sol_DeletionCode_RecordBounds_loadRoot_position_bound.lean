-- Prove2me | solution 1 for DeletionCode.RecordBounds.loadRoot_position_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:01:48.850994+00:00
-- url     : https://prove2.me/submissions/9b2daa37-52ae-4557-a1a6-48ca3405c8f6

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds

set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
variable {B : Type*} [DecidableEq B]
namespace DeletionCode.RecordBounds
theorem _root_.solution (x : Letters) (n a len : ℕ) (s t : Memory) (m : ℕ)
    (hlen : 0 < len) (h : ConcreteFill.loadRoot x n a len s m = some t) : a < n := by
  unfold ConcreteFill.loadRoot at h
  split at h
  · omega
  · contradiction
end DeletionCode.RecordBounds
