-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_TMat_sh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:43:44.248783+00:00
-- url     : https://prove2.me/submissions/cca535e7-06b4-4718-b2f5-b81d2a4069d6

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_minorC_congr

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
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) (ε : ℤ) (J I : TIdx (qc_sh mu ε)) :
    TMat (qc_sh mu ε) J I =
      ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * TMat mu (qc_idxE mu ε J) (qc_idxE mu ε I) := by
  unfold TMat
  rw [← Equiv.prod_comp (qc_colE mu ε)]
  have h1 : qc_sh mu ε (lastIdx n) = ε + mu (lastIdx n) := add_comm _ _
  rw [h1, zpow_add, Units.val_mul, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun c _ => ?_
  exact qc_minorC_congr (qc_colH_sh mu ε c.1) _ _ _ _ _ _
end Formalism.InvariantFactorPaths.ColumnFamilies
