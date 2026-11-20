-- Prove2me | solution 1 for DeletionCode.TraceEditData.position_eq_sourcePrefix_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:47:07.87368+00:00
-- url     : https://prove2.me/submissions/2617fb2e-46ce-43d6-a364-240e392c24bb

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData

set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators
namespace DeletionCode.TraceEditData
theorem _root_.solution (trace : Trace) (c : EditColumn trace) :
    position trace c = (sourcePrefix trace c).length := rfl
end DeletionCode.TraceEditData
