-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_evGL_detU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:53.061976+00:00
-- url     : https://prove2.me/submissions/70640562-5281-4072-90af-217e5ef81200

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type} [CommRing R] (x : GL (Fin n) R) (m : ℤ) :
    evGL x ((detU n ^ m : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((Matrix.GeneralLinearGroup.det x ^ m : Rˣ) : R) := by
  have h : Units.map (evGL x).toMonoidHom (detU n) = Matrix.GeneralLinearGroup.det x := by
    ext
    simp only [Units.coe_map, detU, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Matrix.GeneralLinearGroup.val_det_apply]
    rw [evGL, IsLocalization.Away.lift_eq, RingHom.map_det, genMat_map_eval]
  rw [← h, ← map_zpow]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
