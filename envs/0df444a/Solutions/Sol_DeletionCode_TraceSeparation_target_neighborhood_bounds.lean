-- Prove2me | solution 1 for DeletionCode.TraceSeparation.target_neighborhood_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:47:15.831857+00:00
-- url     : https://prove2.me/submissions/23f52111-5074-45e0-8f77-2de9782eef68

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_targetPosition_margins
import Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_bounds

set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    neighborhoodLeft L (trace.targetPosition i.val) + 2 * L =
        neighborhoodRight L (trace.targetPosition i.val) ∧
      neighborhoodRight L (trace.targetPosition i.val) ≤ trace.target.length :=
  neighborhood_bounds hL (targetPosition_margins hsep i hi)
end DeletionCode.TraceSeparation
