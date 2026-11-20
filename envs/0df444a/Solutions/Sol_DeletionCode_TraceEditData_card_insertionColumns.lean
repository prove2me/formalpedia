-- Prove2me | solution 1 for DeletionCode.TraceEditData.card_insertionColumns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:51:08.067494+00:00
-- url     : https://prove2.me/submissions/b45ac38f-e06a-4501-b9ab-3f2dc1a494f8

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
import Theorems.Thm_DeletionCode_TraceEditData_countP_isInsertion
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans


set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators
namespace DeletionCode.TraceEditData
theorem _root_.solution (trace : Trace) :
    Fintype.card {c : EditColumn trace // orientation trace c = .insertion} = trace.insertions :=
  (Fintype.card_congr (insertionColumnEquiv trace)).trans
    ((card_column_predicate trace isInsertion).trans (countP_isInsertion trace))
end DeletionCode.TraceEditData
