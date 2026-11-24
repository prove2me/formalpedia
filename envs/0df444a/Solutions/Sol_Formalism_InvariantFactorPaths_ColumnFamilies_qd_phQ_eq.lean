-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_phQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:36:03.849104+00:00
-- url     : https://prove2.me/submissions/19f30822-de21-42b7-8c73-bf853bde99fd

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (j : CF.J) (w : TIdx (CF.mu j) → ℚ) :
    qd_phQ CF j w = ∑ I, w I • (fun i => (CF.vec j I i : ℚ)) := by
  funext i
  simp [qd_phQ, Matrix.mulVec, dotProduct, ColFam.vec, Finset.sum_apply, mul_comm]
end Formalism.InvariantFactorPaths.ColumnFamilies
