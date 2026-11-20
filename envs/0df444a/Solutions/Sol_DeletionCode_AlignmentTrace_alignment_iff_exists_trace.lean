-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.alignment_iff_exists_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:57.332827+00:00
-- url     : https://prove2.me/submissions/1853d4e1-e07c-4ae4-b104-4eea7cc34b46

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_alignment
import Theorems.Thm_DeletionCode_AlignmentTrace_exists_trace_of_alignment

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
namespace DeletionCode.AlignmentTrace
theorem _root_.solution (y z : Word) (d i : ℕ) :
    Alignment y z d i ↔
      ∃ trace : Trace, trace.source = y ∧ trace.target = z ∧
        trace.deletions = d ∧ trace.insertions = i := by
  constructor
  · exact exists_trace_of_alignment
  · rintro ⟨trace, rfl, rfl, rfl, rfl⟩
    exact trace.alignment
end DeletionCode.AlignmentTrace
