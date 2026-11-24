-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_det_full
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:27.896503+00:00
-- url     : https://prove2.me/submissions/990e026a-bd7e-45b0-93fb-4f375cc08e78

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
theorem _root_.solution {m : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin m) (Fin m) R) {k : ℕ} (hk : k = m)
    (S : Finset (Fin m)) (hS : S.card = k) :
    (A.submatrix (S.orderEmbOfFin hS) (S.orderEmbOfFin hS)).det = A.det := by
  subst hk
  exact Matrix.det_submatrix_equiv_self
    (Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (S.orderEmbOfFin hS).injective)) A
end Formalism.InvariantFactorPaths.ColumnFamilies
