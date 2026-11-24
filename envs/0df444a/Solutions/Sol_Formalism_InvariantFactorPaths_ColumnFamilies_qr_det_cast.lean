-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_det_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:49.15626+00:00
-- url     : https://prove2.me/submissions/814d7379-301b-4ed1-a60e-5431bed7e1b2

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite

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
variable {m : ℕ} {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hb : IsBlock h g1 t) {k : ℕ} (r c : Fin k → Fin m) :
    (h.val.submatrix (fun a => (r a).castSucc) (fun a => (c a).castSucc)).det = (g1.val.submatrix r c).det := by
  congr 1
  ext a b
  exact hb.1 _ _
end Formalism.InvariantFactorPaths.ColumnFamilies
