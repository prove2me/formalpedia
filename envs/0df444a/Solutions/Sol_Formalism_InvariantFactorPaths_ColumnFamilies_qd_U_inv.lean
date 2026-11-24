-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_U_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:31.10368+00:00
-- url     : https://prove2.me/submissions/443e2ce1-8976-467c-9ea7-821b58c5b553

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_evGLR_mapCoord
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_evGL_detU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra ℚ R'] (x u : GL (Fin n) R') (mu : Fin n → ℤ)
    (hu : Matrix.GeneralLinearGroup.det u = 1) :
    evGLR (R := ℚ) (x * u) (qd_U mu) = evGLR (R := ℚ) x (qd_U mu) := by
  unfold qd_U
  rw [qd_evGLR_mapCoord, qd_evGLR_mapCoord, qd_evGL_detU, qd_evGL_detU, map_mul, hu, mul_one]
end Formalism.InvariantFactorPaths.ColumnFamilies
