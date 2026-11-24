-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_TMat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:58:11.78652+00:00
-- url     : https://prove2.me/submissions/ea386c68-354c-4ab5-90c7-dcebc208518c

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_cb_minor
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_minorC
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_dU_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_detU_zpow

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
theorem _root_.solution {n : ℕ} [NeZero n] (mu : Fin n → ℤ) {R : Type} [CommRing R] (x g : GL (Fin n) R)
    (J I : TIdx mu) :
    evGL (x * g) (TMat mu J I) = ∑ K : TIdx mu, evGL x (TMat mu J K) * evGL g (TMat mu K I) := by
  simp only [TMat, map_mul, map_prod, qc_evGL_detU_zpow, qc_evGL_minorC, qc_dU_mul, mul_zpow, Units.val_mul]
  simp only [qc_cb_minor]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [Finset.prod_mul_distrib]
  ring
end Formalism.InvariantFactorPaths.ColumnFamilies
