-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_raise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:44:38.16468+00:00
-- url     : https://prove2.me/submissions/1a2bd2dd-365c-4a93-b86d-c23aab6b8b36

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_sig_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_sig
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_L_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_trans_det
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_aeval_generic_point
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_aeval_xu
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_U_unit
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_U_inv

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
theorem _root_.solution (mu : Fin n → ℤ) (P : MvPolynomial (Fin n × Fin n) ℚ) (a b : Fin n) (hab : a ≠ b)
    (h : evGLR (R := ℚ) (qd_genPt n * qd_trans a b hab Polynomial.X) (qd_L mu P)
      = evGLR (R := ℚ) (qd_genPt n) (qd_L mu P)) :
    rowGen ℚ a b P = Polynomial.C P := by
  rw [qd_L_apply, map_mul, map_mul, qd_U_inv _ _ _ (qd_trans_det a b hab _)] at h
  have h2 := (qd_U_unit (qd_genPt n) mu).mul_left_cancel h
  rw [qd_ev_sig, qd_ev_sig, aeval_generic_point, qd_aeval_xu] at h2
  apply Polynomial.map_injective (qd_sig n).toRingHom (qd_sig_inj n)
  rw [h2, Polynomial.map_C]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
