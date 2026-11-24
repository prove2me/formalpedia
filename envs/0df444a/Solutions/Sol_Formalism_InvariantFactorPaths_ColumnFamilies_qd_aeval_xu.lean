-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_aeval_xu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:12.230353+00:00
-- url     : https://prove2.me/submissions/67a21652-f41b-4bde-96bc-b0b98737d3cf

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_sig_X
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_genPt_val
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_mul_trans
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowGen_X
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
theorem _root_.solution (a b : Fin n) (hab : a ≠ b) (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (qd_genPt n * qd_trans a b hab Polynomial.X).val v.2 v.1) P
      = Polynomial.map (qd_sig n).toRingHom (rowGen ℚ a b P) := by
  have h : (aeval (R := ℚ)
      (fun v : Fin n × Fin n => (qd_genPt n * qd_trans a b hab Polynomial.X).val v.2 v.1))
      = (Polynomial.mapAlgHom (qd_sig n)).comp (rowGen ℚ a b) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [aeval_X, AlgHom.comp_apply, rowGen_X, qd_mul_trans, Polynomial.coe_mapAlgHom]
    split_ifs <;> simp [qd_sig_X, qd_genPt_val]
  exact congrArg (fun φ => φ P) h
end Formalism.InvariantFactorPaths.ColumnFamilies
