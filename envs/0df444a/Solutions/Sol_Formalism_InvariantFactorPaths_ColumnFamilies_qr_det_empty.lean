-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_det_empty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:49.274709+00:00
-- url     : https://prove2.me/submissions/10ec1572-a9f1-490e-830f-4d2915143b09

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector

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
theorem _root_.solution {m : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin m) (Fin m) R) {k : ℕ} (hk : k = 0)
    (r c : Fin k → Fin m) : (A.submatrix r c).det = 1 := by
  subst hk
  exact Matrix.det_fin_zero
end Formalism.InvariantFactorPaths.ColumnFamilies
