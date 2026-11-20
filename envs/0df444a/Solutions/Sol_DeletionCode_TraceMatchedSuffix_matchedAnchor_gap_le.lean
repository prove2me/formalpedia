-- Prove2me | solution 1 for DeletionCode.TraceMatchedSuffix.matchedAnchor_gap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:45:51.790546+00:00
-- url     : https://prove2.me/submissions/a7ae2aeb-f986-474f-abdc-25a9230800cb

import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Theorems.Thm_DeletionCode_TraceMatchedSuffix_matchedCount_le_length
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedCount_append


set_option autoImplicit true
open DeletionCode DeletionCode.TraceMatchedSuffix
open AlignmentTrace FiniteConflictGraph TraceSeparation
namespace DeletionCode.TraceMatchedSuffix
theorem _root_.solution (trace : Trace) (i j : ℕ) (hij : i ≤ j) :
    trace.matchedAnchor j ≤ trace.matchedAnchor i + (j - i) := by
  have hsplit : trace.take j = trace.take i ++ (trace.drop i).take (j - i) := by
    conv_lhs => rw [show j = i + (j - i) by omega, List.take_add]
  have hcount := congrArg Trace.matchedCount hsplit
  rw [Trace.matchedCount_append] at hcount
  have h := matchedCount_le_length ((trace.drop i).take (j - i))
  have hlen := List.length_take_le (j - i) (trace.drop i)
  change Trace.matchedCount (trace.take j) ≤ Trace.matchedCount (trace.take i) + (j - i)
  omega
end DeletionCode.TraceMatchedSuffix
