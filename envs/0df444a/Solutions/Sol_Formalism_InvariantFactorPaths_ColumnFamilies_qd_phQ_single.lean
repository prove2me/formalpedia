-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_phQ_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:54:02.572824+00:00
-- url     : https://prove2.me/submissions/d2e39e63-6b6e-4521-b33a-26e0f599a8b4

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_phQ_eq
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
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (j : CF.J) (I : TIdx (CF.mu j)) :
    qd_phQ CF j (Pi.single I 1) = fun i => (CF.vec j I i : ℚ) := by
  classical
  rw [qd_phQ_eq]
  simp [Pi.single_apply, ite_smul]
end Formalism.InvariantFactorPaths.ColumnFamilies
