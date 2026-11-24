-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_detU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:12.208501+00:00
-- url     : https://prove2.me/submissions/290bc916-0364-4d1d-b1e3-a8f9eb9bdfa9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_alg
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_detU_coe

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
theorem _root_.solution {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) :
    evGL g ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = g.val.det := by
  rw [qc_detU_coe, qc_evGL_alg, RingHom.map_det, genMat_map_eval]
end Formalism.InvariantFactorPaths.ColumnFamilies
