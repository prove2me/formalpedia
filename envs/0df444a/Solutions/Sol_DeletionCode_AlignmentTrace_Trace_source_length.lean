-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.source_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:24:42.702109+00:00
-- url     : https://prove2.me/submissions/c1febf8d-dc8b-4c77-a17d-b63454134c84

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (trace : Trace) :
    trace.source.length = trace.matchedCount + trace.deletions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;> simp only [source, matchedCount, deletions, List.length_cons] <;> omega
end DeletionCode.AlignmentTrace.Trace
