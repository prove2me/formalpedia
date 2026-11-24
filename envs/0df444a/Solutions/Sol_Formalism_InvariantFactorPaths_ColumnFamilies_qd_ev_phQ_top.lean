-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_phQ_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:12:13.973056+00:00
-- url     : https://prove2.me/submissions/f546c55d-0748-484d-aba0-0b1907f0f55f

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_phQ
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_key_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_Lam_apply
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
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (j : CF.J) (w : TIdx (CF.mu j) → ℚ)
    (hw : qd_Lam (CF.mu j) w = 0) : qb_ev M ℚ (CF.mu j) (qd_phQ CF j w) = 0 := by
  funext i
  rw [qd_ev_phQ]
  simp only [qb_key_eq, ← mul_smul_comm]
  rw [← Finset.mul_sum, ← qd_Lam_apply, hw, mul_zero, Pi.zero_apply]
end Formalism.InvariantFactorPaths.ColumnFamilies
