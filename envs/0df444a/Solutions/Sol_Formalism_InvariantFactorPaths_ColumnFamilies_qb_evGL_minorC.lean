-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_evGL_minorC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:28.603801+00:00
-- url     : https://prove2.me/submissions/18bc604a-3cb2-49fb-bb5c-b9f9b304da05

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evGL_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type} [CommRing R] (g : GL (Fin n) R) {h : ℕ} (J I : Finset (Fin n))
    (hJ : J.card = h) (hI : I.card = h) :
    evGL g (minorC J I hJ hI) =
      Matrix.det (Matrix.of fun a b : Fin h => g.val (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) := by
  unfold minorC
  rw [qb_evGL_algebraMap, RingHom.map_det]
  congr 1
  ext a b
  simp [genMat]
end Formalism.InvariantFactorPaths.ColumnFamilies
