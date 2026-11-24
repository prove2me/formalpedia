-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_genPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:43:47.940999+00:00
-- url     : https://prove2.me/submissions/6591e5cf-ba66-4ada-843e-8c9909e71101

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_genPt_val
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_mapCoord_alg
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_hom_ext
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
theorem _root_.solution (F : Type) [CommRing F] (n : ℕ) : evGL (qc_genPt F n) = mapCoord F := by
  apply qc_hom_ext
  intro a b
  rw [qc_evGL_alg, qc_mapCoord_alg]
  simp [qc_genPt_val]
end Formalism.InvariantFactorPaths.ColumnFamilies
