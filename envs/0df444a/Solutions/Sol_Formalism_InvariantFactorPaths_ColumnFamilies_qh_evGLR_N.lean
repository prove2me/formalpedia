-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_evGLR_N
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:23.698101+00:00
-- url     : https://prove2.me/submissions/d24655bc-de96-4132-93e5-ea883829defb

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_prod_castLE
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_evGLR_alg

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
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra R R'] (g : GL (Fin n) R') (s : ℕ) (hs : s ≤ n)
    (J : Fin s → Fin n) :
    evGLR g (qhN R s hs J) = Matrix.det (Matrix.of fun p q : Fin s => g.val (Fin.castLE hs p) (J q)) := by
  rw [qhN, qh_evGLR_alg, RingHom.map_det]
  congr 1
  ext p q
  simp [genMat]
end Formalism.InvariantFactorPaths.ColumnFamilies
