-- Prove2me | solution 1 for DeletionCode.AnchorRecords.get_recordIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:58:14.588152+00:00
-- url     : https://prove2.me/submissions/3fbef3ef-ce8e-4c67-920c-e44a8358d58f

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
import Theorems.Thm_DeletionCode_AnchorRecords_packetAt_recordRank

set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData
namespace DeletionCode.AnchorRecords
theorem _root_.solution (trace : Trace) (c : EditColumn trace) :
    (encode trace).get (recordIndex trace c) =
      (trace.matchedAnchor c.val.val, payload (column trace c)) := by
  have h := packetAt_recordRank trace c
  rw [List.getElem?_eq_getElem (recordRank_lt trace c)] at h
  exact Option.some.inj h
end DeletionCode.AnchorRecords
