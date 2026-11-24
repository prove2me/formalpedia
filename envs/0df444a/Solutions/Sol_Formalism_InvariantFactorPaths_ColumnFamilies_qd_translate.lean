-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:47.729505+00:00
-- url     : https://prove2.me/submissions/0eeb1abd-272a-4219-814c-e815f81ce5dd

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_evGL_map
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_algebraMap
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_L_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_L_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_TMat_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_L_P
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_evGLR_mapCoord


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
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) (γ : GL (Fin n) ℚ) :
    ∑ K, qd_gcan mu γ K • qd_P mu K =
      ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ) • rowAct ℚ γ.val.transpose (qd_P mu (canT mu)) := by
  apply qd_L_inj mu
  rw [← qd_ev_L_mul, qd_L_P, qd_evGLR_mapCoord, brk, qc_TMat_mul, map_sum, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, qd_L_P, Algebra.smul_def, map_mul, qd_evGLR_mapCoord, qd_evGL_map, mul_comm]
  rw [qd_ev_algebraMap]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
