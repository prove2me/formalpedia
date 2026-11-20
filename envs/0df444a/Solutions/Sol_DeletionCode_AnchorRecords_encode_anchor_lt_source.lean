-- Prove2me | solution 1 for DeletionCode.AnchorRecords.encode_anchor_lt_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:59:41.977742+00:00
-- url     : https://prove2.me/submissions/7f576ee5-fc3d-4502-9be5-0e9f3994b236

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
import Theorems.Thm_DeletionCode_AnchorRecords_encode_anchor_le
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_source_length


set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData
namespace DeletionCode.AnchorRecords
theorem _root_.solution (trace : Trace) (hd : 1 ≤ trace.deletions)
    (p : Packet) (hp : p ∈ encode trace) : p.1 < trace.source.length := by
  have ha := encode_anchor_le trace p hp
  have hn := trace.source_length
  omega
end DeletionCode.AnchorRecords
