-- Prove2me | solution 1 for DeletionCode.TraceSeparation.target_neighborhood_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:56:43.378627+00:00
-- url     : https://prove2.me/submissions/d73e4047-3b42-4b34-ade1-d41fe20893e4

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_targetPosition_separated
import Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_disjoint_of_gap
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm


set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hne : i ≠ j) :
    Disjoint (neighborhood L (trace.targetPosition i.val))
      (neighborhood L (trace.targetPosition j.val)) := by
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  by_cases hij : i.val < j.val
  · exact neighborhood_disjoint_of_gap hL (targetPosition_separated hsep i j hi hj hij)
  · exact (neighborhood_disjoint_of_gap hL
      (targetPosition_separated hsep j i hj hi (by omega))).symm
end DeletionCode.TraceSeparation
