-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.exists_trace_of_alignment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:27:21.681225+00:00
-- url     : https://prove2.me/submissions/bf7006a3-501b-46dd-bded-29eadb755c13

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_zero
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_end

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
namespace DeletionCode.AlignmentTrace
theorem _root_.solution {y z : Word} {d i : ℕ}
    (h : Alignment y z d i) :
    ∃ trace : Trace, trace.source = y ∧ trace.target = z ∧
      trace.deletions = d ∧ trace.insertions = i := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, rfl, rfl⟩
  | matched bit h ih =>
    obtain ⟨trace, hs, ht, hd, hi⟩ := ih
    refine ⟨Column.matched bit :: trace, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Trace.source, Trace.target, Trace.deletions, Trace.insertions, hs, ht, hd, hi]
  | deletion bit h ih =>
    obtain ⟨trace, hs, ht, hd, hi⟩ := ih
    refine ⟨Column.deletion bit :: trace, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Trace.source, Trace.target, Trace.deletions, Trace.insertions, hs, ht, hd, hi]
  | insertion bit h ih =>
    obtain ⟨trace, hs, ht, hd, hi⟩ := ih
    refine ⟨Column.insertion bit :: trace, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Trace.source, Trace.target, Trace.deletions, Trace.insertions, hs, ht, hd, hi]
end DeletionCode.AlignmentTrace
