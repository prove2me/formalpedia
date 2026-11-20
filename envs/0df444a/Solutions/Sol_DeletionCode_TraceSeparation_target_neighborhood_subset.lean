-- Prove2me | solution 1 for DeletionCode.TraceSeparation.target_neighborhood_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:47:37.773958+00:00
-- url     : https://prove2.me/submissions/1da46bad-f258-423c-999e-26954c0e517b

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_targetPosition_margins
import Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_subset

set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    neighborhood L (trace.targetPosition i.val) ⊆ Set.Ico 0 trace.target.length :=
  neighborhood_subset hL (targetPosition_margins hsep i hi)
end DeletionCode.TraceSeparation
