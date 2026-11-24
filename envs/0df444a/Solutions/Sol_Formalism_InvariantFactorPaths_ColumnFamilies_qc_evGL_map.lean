-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:34.450219+00:00
-- url     : https://prove2.me/submissions/4bcef149-c05b-4911-b469-1073f1f673f7

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
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
theorem _root_.solution {n : ℕ} {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (g : GL (Fin n) R) :
    evGL (Matrix.GeneralLinearGroup.map φ g) = φ.comp (evGL g) := by
  apply qc_hom_ext
  intro a b
  rw [RingHom.comp_apply, qc_evGL_alg, qc_evGL_alg]
  simp only [coe_eval₂Hom, eval₂_X]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
