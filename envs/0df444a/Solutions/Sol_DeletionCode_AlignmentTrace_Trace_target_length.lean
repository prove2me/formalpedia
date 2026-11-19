-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.target_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:32:23.618149+00:00
-- url     : https://prove2.me/submissions/25bb6180-2dac-4dfd-a39d-26b658d1ba86

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (trace : Trace) :
    trace.target.length = trace.matchedCount + trace.insertions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;> simp only [target, matchedCount, insertions, List.length_cons] <;> omega
end DeletionCode.AlignmentTrace.Trace
