-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.aeval_generic_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:17.981415+00:00
-- url     : https://prove2.me/submissions/5a541968-2477-4d39-ae96-ca048c8038ca

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_sig_X
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_genPt_val
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (qd_genPt n).val v.2 v.1) P = Polynomial.C (qd_sig n P) := by
  have h : (aeval (R := ℚ) (fun v : Fin n × Fin n => (qd_genPt n).val v.2 v.1))
      = (Polynomial.CAlgHom (R := ℚ) (A := GLCoord ℚ n)).comp (qd_sig n) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [qd_sig_X, qd_genPt_val]
  exact congrArg (fun φ => φ P) h
end Formalism.InvariantFactorPaths.ColumnFamilies
