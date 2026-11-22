-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_minorC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:46.320709+00:00
-- url     : https://prove2.me/submissions/0afcef8f-cde5-4114-baa0-6b3682452130

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_alg

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
theorem _root_.solution {n h : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) (J I : Finset (Fin n))
    (hJ : J.card = h) (hI : I.card = h) :
    evGL g (minorC J I hJ hI) = (g.val.submatrix (J.orderEmbOfFin hJ) (I.orderEmbOfFin hI)).det := by
  rw [minorC, qc_evGL_alg, RingHom.map_det]
  congr 1
  ext a b
  simp [genMat]
end Formalism.InvariantFactorPaths.ColumnFamilies
