-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_deriv_rowGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:06.00184+00:00
-- url     : https://prove2.me/submissions/5b4623f8-166e-477d-982d-c4d898d30adf

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
theorem _root_.solution (n : ℕ) (a b : Fin n) (hab : a ≠ b) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    Polynomial.derivative (rowGen ℚ a b (transposeVariables ℚ n f)) = rowGen ℚ a b (transposeVariables ℚ n (qn_D n a b f)) := by
  have hX : ∀ i : Fin n × Fin n, Polynomial.derivative (rowGen ℚ a b (transposeVariables ℚ n (X i))) =
      rowGen ℚ a b (transposeVariables ℚ n (qn_D n a b (X i))) := by
    rintro ⟨l, c⟩
    rw [qn_D_X, qn_T_X]
    by_cases hc : c = b
    · subst hc
      simp [rowGen, qn_T_X, hab]
    · simp [rowGen, hc]
  induction f using MvPolynomial.induction_on with
  | C r =>
    have hD : qn_D n a b (C r) = 0 := by
      rw [qn_D_apply]
      simp
    rw [hD]
    simp [transposeVariables, rowGen]
  | add p q hp hq =>
    simp only [map_add, Polynomial.derivative_add, hp, hq]
  | mul_X p i hp =>
    have hL : qn_D n a b (p * X i) = p * qn_D n a b (X i) + X i * qn_D n a b p := by
      rw [Derivation.leibniz]
      simp [smul_eq_mul]
    rw [hL]
    simp only [map_add, map_mul, Polynomial.derivative_mul, hp, hX i]
    ring
end Formalism.InvariantFactorPaths.ColumnFamilies
