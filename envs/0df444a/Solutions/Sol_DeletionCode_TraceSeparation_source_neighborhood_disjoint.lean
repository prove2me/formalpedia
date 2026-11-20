-- Prove2me | solution 1 for DeletionCode.TraceSeparation.source_neighborhood_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:56:04.13829+00:00
-- url     : https://prove2.me/submissions/97c618fa-cd65-44bf-847b-6f9792926c70

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_sourcePosition_separated
import Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_disjoint_of_gap
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm


set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hne : i ≠ j) :
    Disjoint (neighborhood L (trace.sourcePosition i.val))
      (neighborhood L (trace.sourcePosition j.val)) := by
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  by_cases hij : i.val < j.val
  · exact neighborhood_disjoint_of_gap hL (sourcePosition_separated hsep i j hi hj hij)
  · exact (neighborhood_disjoint_of_gap hL
      (sourcePosition_separated hsep j i hj hi (by omega))).symm
end DeletionCode.TraceSeparation
