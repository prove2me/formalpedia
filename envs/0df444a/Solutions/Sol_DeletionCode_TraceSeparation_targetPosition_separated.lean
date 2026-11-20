-- Prove2me | solution 1 for DeletionCode.TraceSeparation.targetPosition_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:54:30.879178+00:00
-- url     : https://prove2.me/submissions/fdaf443d-a1e6-40be-899a-df346db0f1fb

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_targetPosition_gap

set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {trace : Trace} {B : ℕ}
    (hsep : Separated B trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hij : i.val < j.val) :
    trace.targetPosition i.val + B ≤ trace.targetPosition j.val :=
  targetPosition_gap trace (Nat.le_of_lt hij) (hsep.2 i j hi hj hij)
end DeletionCode.TraceSeparation
