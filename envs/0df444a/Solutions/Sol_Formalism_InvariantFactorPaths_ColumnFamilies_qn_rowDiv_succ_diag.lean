-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_rowDiv_succ_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:15.238743+00:00
-- url     : https://prove2.me/submissions/fedd60f4-52fa-4eb4-b575-c96cef899af0

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_deriv_rowGen_diag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (a : Fin n) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    ((k + 1 : ℕ) : ℚ) • rowDiv ℚ a a (k + 1) (transposeVariables ℚ n f) =
      rowDiv ℚ a a k (transposeVariables ℚ n (qn_D n a a f - (k : ℚ) • f)) := by
  unfold rowDiv
  rw [map_sub, map_smul, map_sub, map_smul, ← qn_deriv_rowGen_diag n a f, Polynomial.coeff_sub,
    Polynomial.coeff_smul, add_mul, one_mul, Polynomial.coeff_add]
  cases k with
  | zero =>
    rw [Polynomial.coeff_X_mul_zero, Polynomial.coeff_derivative]
    simp
  | succ m =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    simp only [MvPolynomial.smul_eq_C_mul, map_natCast, Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring
end Formalism.InvariantFactorPaths.ColumnFamilies
