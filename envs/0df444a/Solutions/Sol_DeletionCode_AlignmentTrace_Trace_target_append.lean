-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.target_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:33:52.871703+00:00
-- url     : https://prove2.me/submissions/73d239a2-80b5-46ec-b99b-b5da3eac58ad

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (left right : Trace) :
    target (left ++ right) = target left ++ target right := by
  induction left with
  | nil => rfl
  | cons col rest ih => cases col <;> simp [target, ih]
end DeletionCode.AlignmentTrace.Trace
