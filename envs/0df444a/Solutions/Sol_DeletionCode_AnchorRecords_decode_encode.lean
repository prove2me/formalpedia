-- Prove2me | solution 1 for DeletionCode.AnchorRecords.decode_encode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:00:03.442567+00:00
-- url     : https://prove2.me/submissions/85e76c7d-4c81-4907-a4f2-b5a4c114d1ef

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
import Theorems.Thm_DeletionCode_AnchorRecords_decodeFrom_encodeFrom

set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData
namespace DeletionCode.AnchorRecords
theorem _root_.solution (trace : Trace) : decode trace.source (encode trace) = trace.target :=
  decodeFrom_encodeFrom trace 0
end DeletionCode.AnchorRecords
