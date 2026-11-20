-- Prove2me | solution 1 for DeletionCode.TraceEditData.split_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:46:48.426385+00:00
-- url     : https://prove2.me/submissions/09a5f523-d02b-4ece-bc6f-aaf101858e2d

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm


set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators
namespace DeletionCode.TraceEditData
theorem _root_.solution (trace : Trace) (c : EditColumn trace) :
    trace = trace.take c.val.val ++ column trace c :: trace.drop (c.val.val + 1) := by
  have hd : trace.drop c.val.val = column trace c :: trace.drop (c.val.val + 1) :=
    List.drop_eq_getElem_cons c.val.isLt
  calc
    trace = trace.take c.val.val ++ trace.drop c.val.val :=
      (List.take_append_drop c.val.val trace).symm
    _ = _ := by rw [hd]
end DeletionCode.TraceEditData
