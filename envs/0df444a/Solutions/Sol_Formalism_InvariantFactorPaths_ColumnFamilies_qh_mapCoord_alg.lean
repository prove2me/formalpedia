-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_mapCoord_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:24.981946+00:00
-- url     : https://prove2.me/submissions/a9f3c87a-f0f8-4540-b7b5-5d9c27442f9d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount

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
theorem _root_.solution (P : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) R (algebraMap _ _ P) = algebraMap _ _ (MvPolynomial.map (Int.castRingHom R) P) := by
  first
    | (rw [mapCoord, IsLocalization.Away.AwayMap.lift_eq]; try rfl; done)
    | (rw [mapCoord, IsLocalization.Away.lift_eq]; try rfl; done)
    | (simp [mapCoord]; done)
    | (unfold mapCoord; exact IsLocalization.lift_eq _ _)
end Formalism.InvariantFactorPaths.ColumnFamilies
