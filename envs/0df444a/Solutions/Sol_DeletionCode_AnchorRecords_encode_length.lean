-- Prove2me | solution 1 for DeletionCode.AnchorRecords.encode_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:57:05.138204+00:00
-- url     : https://prove2.me/submissions/2691d9bd-2aae-4f2b-bca9-ac38e1ff72ed

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
import Theorems.Thm_DeletionCode_AnchorRecords_encodeFrom_length

set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData
namespace DeletionCode.AnchorRecords
theorem _root_.solution (trace : Trace) :
    (encode trace).length = trace.deletions + trace.insertions := encodeFrom_length trace 0
end DeletionCode.AnchorRecords
