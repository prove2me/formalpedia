-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_evGLR_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:51.806029+00:00
-- url     : https://prove2.me/submissions/fc7d8dda-cbf0-466f-b35a-064670fb3e4f

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_evGLR_alg
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
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra R R'] (g : GL (Fin n) R') :
    evGLR g ((qhDet R n : (GLCoord R n)ˣ) : GLCoord R n) = g.val.det := by
  rw [qhDet_val, qh_evGLR_alg, RingHom.map_det, genMat_map_evalR]
end Formalism.InvariantFactorPaths.ColumnFamilies
