-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_phQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:54:17.26805+00:00
-- url     : https://prove2.me/submissions/d936dafe-aa23-46d9-80a7-3e72d79eb10c

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_phQ_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evL_apply
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
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (j : CF.J) (nu : Fin n → ℤ) (w : TIdx (CF.mu j) → ℚ) (i : M.ι) :
    qb_ev M ℚ nu (qd_phQ CF j w) i = ∑ I, w I • qb_ev M ℚ nu (fun i => (CF.vec j I i : ℚ)) i := by
  rw [qd_phQ_eq, ← qb_evL_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, qb_evL_apply, Pi.smul_apply]
end Formalism.InvariantFactorPaths.ColumnFamilies
