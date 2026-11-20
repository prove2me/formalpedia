-- Prove2me | solution 1 for DeletionCode.TraceSeparation.source_neighborhood_ordered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:56:05.793973+00:00
-- url     : https://prove2.me/submissions/d717c0e0-87bb-40e3-a3bb-6ebafc6bdba2

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_sourcePosition_separated
import Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_ordered

set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hij : i.val < j.val) :
    neighborhoodRight L (trace.sourcePosition i.val) ≤
      neighborhoodLeft L (trace.sourcePosition j.val) :=
  neighborhood_ordered hL (sourcePosition_separated hsep i j hi hj hij)
end DeletionCode.TraceSeparation
