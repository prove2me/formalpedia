-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_brk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:31.616264+00:00
-- url     : https://prove2.me/submissions/688703b2-157b-4676-ad20-04e5010c8d68

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_sig_X
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_can_emb
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
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) (I : TIdx mu) :
    mapCoord ℚ (brk mu I) = qd_U mu * qd_sig n (qd_P mu I) := by
  unfold brk TMat qd_U qd_P
  rw [map_mul, map_prod, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold minorC initMinor
  rw [mapCoord, IsLocalization.Away.lift_eq, RingHom.comp_apply, RingHom.map_det, AlgHom.map_det,
    RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext a b
  simp [genMat, qd_can_emb, qd_sig_X]
end Formalism.InvariantFactorPaths.ColumnFamilies
