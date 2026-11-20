-- Prove2me | solution 1 for DeletionCode.TraceSeparation.source_neighborhood_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:47:36.646041+00:00
-- url     : https://prove2.me/submissions/df6f9ae6-028c-43df-8f86-8abf0e87c009

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_sourcePosition_margins
import Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_bounds

set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    neighborhoodLeft L (trace.sourcePosition i.val) + 2 * L =
        neighborhoodRight L (trace.sourcePosition i.val) ∧
      neighborhoodRight L (trace.sourcePosition i.val) ≤ trace.source.length :=
  neighborhood_bounds hL (sourcePosition_margins hsep i hi)
end DeletionCode.TraceSeparation
