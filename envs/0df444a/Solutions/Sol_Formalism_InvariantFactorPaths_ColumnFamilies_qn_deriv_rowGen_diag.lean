-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_deriv_rowGen_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:52.039426+00:00
-- url     : https://prove2.me/submissions/390c4daf-3b54-4d99-83ef-5e9f14fc93ce

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_T_X
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_D_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_D_X
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
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (a : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    (1 + Polynomial.X) * Polynomial.derivative (rowGen ℚ a a (transposeVariables ℚ n f)) =
      rowGen ℚ a a (transposeVariables ℚ n (qn_D n a a f)) := by
  have hX : ∀ i : Fin n × Fin n, (1 + Polynomial.X) * Polynomial.derivative (rowGen ℚ a a (transposeVariables ℚ n (X i))) =
      rowGen ℚ a a (transposeVariables ℚ n (qn_D n a a (X i))) := by
    rintro ⟨l, c⟩
    rw [qn_D_X, qn_T_X]
    by_cases hc : c = a
    · subst hc
      simp [rowGen, qn_T_X]
      ring
    · simp [rowGen, hc]
  induction f using MvPolynomial.induction_on with
  | C r =>
    have hD : qn_D n a a (C r) = 0 := by
      rw [qn_D_apply]
      simp
    rw [hD]
    simp [transposeVariables, rowGen]
  | add p q hp hq =>
    simp only [map_add, Polynomial.derivative_add, mul_add, hp, hq]
  | mul_X p i hp =>
    have hL : qn_D n a a (p * X i) = p * qn_D n a a (X i) + X i * qn_D n a a p := by
      rw [Derivation.leibniz]
      simp [smul_eq_mul]
    rw [hL, map_mul, map_mul, Polynomial.derivative_mul, mul_add, ← mul_assoc,
      mul_left_comm (1 + Polynomial.X) (rowGen ℚ a a (transposeVariables ℚ n p)), hp, hX i]
    simp only [map_add, map_mul]
    ring
end Formalism.InvariantFactorPaths.ColumnFamilies
