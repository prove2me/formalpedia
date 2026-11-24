-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_evGLR_algR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:23.712392+00:00
-- url     : https://prove2.me/submissions/28bde932-dd67-49f6-b376-fa9220e9d559

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
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra R R'] (g : GL (Fin n) R') (r : R) :
    evGLR g (algebraMap R (GLCoord R n) r) = algebraMap R R' r := by
  rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n), qh_evGLR_alg]
  simp
end Formalism.InvariantFactorPaths.ColumnFamilies
