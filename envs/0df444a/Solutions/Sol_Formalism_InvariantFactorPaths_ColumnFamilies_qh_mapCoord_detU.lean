-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_mapCoord_detU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:22.541726+00:00
-- url     : https://prove2.me/submissions/f3f7d9a7-5cab-4753-89fa-a929f08e3492

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mapCoord_alg
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qhDet_val


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
theorem _root_.solution (z : ℤ) :
    mapCoord R ((detU n ^ z : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((qhDet R n ^ z : (GLCoord R n)ˣ) : GLCoord R n) := by
  have h1 : Units.map (mapCoord (n := n) R).toMonoidHom (detU n) = qhDet R n := by
    apply Units.ext
    rw [Units.coe_map, qhDet_val]
    show mapCoord (n := n) R (algebraMap _ _ (genMat ℤ n).det) = _
    rw [qh_mapCoord_alg, RingHom.map_det (MvPolynomial.map (Int.castRingHom R)) (genMat ℤ n),
      genMat_map_coord]
  rw [← h1, ← map_zpow (Units.map (mapCoord (n := n) R).toMonoidHom) (detU n) z, Units.coe_map]
  try rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
