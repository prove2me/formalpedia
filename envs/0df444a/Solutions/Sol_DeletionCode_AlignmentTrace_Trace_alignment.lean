-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.alignment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:01.13369+00:00
-- url     : https://prove2.me/submissions/7215ccab-e92b-4911-97b9-b7dbdacb15d0

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (trace : Trace) :
    Alignment trace.source trace.target trace.deletions trace.insertions := by
  induction trace with
  | nil => exact Alignment.nil
  | cons col rest ih =>
    cases col with
    | matched bit => exact Alignment.matched bit ih
    | deletion bit => exact Alignment.deletion bit ih
    | insertion bit => exact Alignment.insertion bit ih
end DeletionCode.AlignmentTrace.Trace
