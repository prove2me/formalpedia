-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_fact_rowDiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:15.252648+00:00
-- url     : https://prove2.me/submissions/9a3ca85c-ba32-465a-ac95-88ec29703229

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_rowDiv_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_rowDiv_succ
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_E_eq
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
theorem _root_.solution (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :
    ∀ f : MvPolynomial (Fin n × Fin n) ℚ,
    (k.factorial : ℚ) • rowDiv ℚ a b k (transposeVariables ℚ n f) =
      transposeVariables ℚ n (((glOps ℚ n (rowLetters n) Set.univ a b) ^ k) f) := by
  induction k with
  | zero =>
    intro f
    simp [qn_rowDiv_zero]
  | succ k ih =>
    intro f
    rw [Nat.factorial_succ, Nat.cast_mul, mul_comm ((k + 1 : ℕ) : ℚ), mul_smul, qn_rowDiv_succ n a b hab k f,
      ih, pow_succ, Module.End.mul_apply, qn_E_eq]
end Formalism.InvariantFactorPaths.ColumnFamilies
