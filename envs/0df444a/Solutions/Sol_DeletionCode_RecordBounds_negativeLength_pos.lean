-- Prove2me | solution 1 for DeletionCode.RecordBounds.negativeLength_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:00:51.053952+00:00
-- url     : https://prove2.me/submissions/efcc5d74-83a8-426e-8e99-ac16613e3623

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
import Theorems.Thm_DeletionCode_HeaderRecovery_negativeLength_eq


set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
namespace DeletionCode.RecordBounds
theorem _root_.solution (k : ℕ) (h : Header)
    (hlo : 1 ≤ h.rho) (hhi : h.rho ≤ k + 1) : 0 < negativeLength k h := by
  rw [negativeLength_eq k h hlo hhi]
  unfold windowLength
  omega
end DeletionCode.RecordBounds
