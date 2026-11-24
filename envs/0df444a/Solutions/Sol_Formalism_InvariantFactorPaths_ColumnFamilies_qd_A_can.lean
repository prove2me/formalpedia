-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_A_can
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:36:02.85581+00:00
-- url     : https://prove2.me/submissions/4543da4e-7f7c-44e0-98aa-755b5eb78d8e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_equiv_apply
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
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (j : CF.J) (g : GL (Fin n) ℚ) :
    Matrix.mulVec (M.A.map (evGL g)) (fun i => (CF.vec j (canT (CF.mu j)) i : ℚ)) =
      qd_phQ CF j (qd_gcan (CF.mu j) g) := by
  funext i
  have h := congrArg (evGL g) (qb_equiv_apply CF j i (canT (CF.mu j)))
  simp only [map_sum, map_mul, map_intCast] at h
  simpa [Matrix.mulVec, dotProduct, ColFam.vec, qd_phQ, qd_gcan] using h
end Formalism.InvariantFactorPaths.ColumnFamilies
