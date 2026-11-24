-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_mapCoord_minor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:01.507659+00:00
-- url     : https://prove2.me/submissions/b22f14bd-b187-4b25-9dee-55c192df7506

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mapCoord_alg
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_can_emb

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
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (S : Finset (Fin n))
    (hS : S.card = colH mu c) :
    mapCoord R (minorC (canT mu c).1 S (canT mu c).2 hS) =
      qhN R (colH mu c) (colH_le mu c) (fun q => S.orderEmbOfFin hS q) := by
  unfold minorC qhN
  rw [qh_mapCoord_alg, RingHom.map_det (MvPolynomial.map (Int.castRingHom R))]
  congr 2
  ext p q
  first
    | (simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, genMat, MvPolynomial.map_X,
        qh_can_emb]; done)
    | simp [genMat, qh_can_emb]
end Formalism.InvariantFactorPaths.ColumnFamilies
