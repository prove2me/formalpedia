-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_trans_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:36.97985+00:00
-- url     : https://prove2.me/submissions/0a54404d-e1bb-4d26-87ee-175850624a0d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant

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
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type} [CommRing R] (a b : Fin n) (hab : a ≠ b) (t : R) :
    Matrix.GeneralLinearGroup.det (qd_trans a b hab t) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_transvection_of_ne _ _ hab t
end Formalism.InvariantFactorPaths.ColumnFamilies
