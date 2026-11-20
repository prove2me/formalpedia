-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.trace_of_equal_length_confusability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:54.927043+00:00
-- url     : https://prove2.me/submissions/4a3f3a42-5f20-492a-a099-6733da8b4260

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
import Theorems.Thm_DeletionCode_AlignmentTrace_exists_trace_of_alignment
import Theorems.Thm_DeletionCode_EditAlignment_equal_length_confusability


set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
namespace DeletionCode.AlignmentTrace
theorem _root_.solution (y z u : Word) (n t : ℕ)
    (hy : y.length = n) (hz : z.length = n)
    (hyu : WithinEdits t y u) (hzu : WithinEdits t z u) :
    ∃ (d : ℕ) (trace : Trace), d ≤ t ∧ trace.source = y ∧ trace.target = z ∧
      trace.deletions = d ∧ trace.insertions = d := by
  obtain ⟨d, hd, halign⟩ := equal_length_confusability y z u n t hy hz hyu hzu
  obtain ⟨trace, hs, ht, hdel, hins⟩ := exists_trace_of_alignment halign
  exact ⟨d, trace, hd, hs, ht, hdel, hins⟩
end DeletionCode.AlignmentTrace
