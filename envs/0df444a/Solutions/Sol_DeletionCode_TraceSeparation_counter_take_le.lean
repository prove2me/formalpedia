-- Prove2me | solution 1 for DeletionCode.TraceSeparation.counter_take_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:36:39.218172+00:00
-- url     : https://prove2.me/submissions/d34eadf0-4ac8-44eb-bf4b-914f5c1a2aed

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation

set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution (counter : Trace → ℕ)
    (happend : ∀ a b, counter (a ++ b) = counter a + counter b)
    (trace : Trace) (i : ℕ) : counter (trace.take i) ≤ counter trace := by
  have h := happend (trace.take i) (trace.drop i)
  rw [List.take_append_drop] at h
  omega
end DeletionCode.TraceSeparation
