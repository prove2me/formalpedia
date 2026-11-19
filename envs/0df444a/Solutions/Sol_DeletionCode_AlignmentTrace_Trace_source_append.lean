-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.source_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:33:50.431812+00:00
-- url     : https://prove2.me/submissions/bde7bbd2-816e-4ecf-b654-3ac8f922d4c8

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (left right : Trace) :
    source (left ++ right) = source left ++ source right := by
  induction left with
  | nil => rfl
  | cons col rest ih => cases col <;> simp [source, ih]
end DeletionCode.AlignmentTrace.Trace
