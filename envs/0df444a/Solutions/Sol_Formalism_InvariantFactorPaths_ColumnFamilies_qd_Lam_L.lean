-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_Lam_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:43:47.186399+00:00
-- url     : https://prove2.me/submissions/79dea644-3a71-4229-a719-c98b81c24c5c

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_Lam_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_L_P


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
theorem _root_.solution (mu : Fin n → ℤ) (w : TIdx mu → ℚ) : qd_Lam mu w = qd_L mu (∑ K, w K • qd_P mu K) := by
  rw [qd_Lam_apply, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, qd_L_P]
end Formalism.InvariantFactorPaths.ColumnFamilies
