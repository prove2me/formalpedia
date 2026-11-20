-- Prove2me | solution 1 for DeletionCode.TraceEditData.card_deletionColumns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:51:07.194124+00:00
-- url     : https://prove2.me/submissions/00f483b4-751e-4ccd-abc1-0bb44d6483c0

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
import Theorems.Thm_DeletionCode_TraceEditData_countP_isDeletion
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans


set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators
namespace DeletionCode.TraceEditData
theorem _root_.solution (trace : Trace) :
    Fintype.card {c : EditColumn trace // orientation trace c = .deletion} = trace.deletions :=
  (Fintype.card_congr (deletionColumnEquiv trace)).trans
    ((card_column_predicate trace isDeletion).trans (countP_isDeletion trace))
end DeletionCode.TraceEditData
