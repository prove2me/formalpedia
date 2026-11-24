-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_L_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:43:45.617692+00:00
-- url     : https://prove2.me/submissions/dc5368b1-940e-4c5e-938a-b96d3fe61e19

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_aeval_generic_point
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_L_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_U_unit
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_sig
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_sig_inj


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
theorem _root_.solution (mu : Fin n → ℤ) (P Q : MvPolynomial (Fin n × Fin n) ℚ)
    (h : evGLR (R := ℚ) (qd_genPt n) (qd_L mu P) = evGLR (R := ℚ) (qd_genPt n) (qd_L mu Q)) : P = Q := by
  rw [qd_L_apply, qd_L_apply, map_mul, map_mul] at h
  have h2 := (qd_U_unit (qd_genPt n) mu).mul_left_cancel h
  rw [qd_ev_sig, qd_ev_sig, aeval_generic_point, aeval_generic_point] at h2
  exact qd_sig_inj n (Polynomial.C_injective h2)
end Formalism.InvariantFactorPaths.ColumnFamilies
