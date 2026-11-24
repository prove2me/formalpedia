-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_dU_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:20.125439+00:00
-- url     : https://prove2.me/submissions/cacb6e5c-5e7d-4ed5-b214-d086cf433d87

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_dU_coe

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} {R : Type} [CommRing R] (x g : GL (Fin n) R) : qc_dU (x * g) = qc_dU x * qc_dU g := by
  apply Units.ext
  rw [Units.val_mul, qc_dU_coe, qc_dU_coe, qc_dU_coe, Units.val_mul, Matrix.det_mul]
end Formalism.InvariantFactorPaths.ColumnFamilies
