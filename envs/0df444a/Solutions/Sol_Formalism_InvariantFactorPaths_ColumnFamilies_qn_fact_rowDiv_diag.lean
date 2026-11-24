-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_fact_rowDiv_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:44.738813+00:00
-- url     : https://prove2.me/submissions/c5e1a802-c5ee-4d76-a324-ca968b039c88

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_rowDiv_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_rowDiv_succ_diag
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
theorem _root_.solution (n : ℕ) (a : Fin n) (k : ℕ) :
    ∀ f : MvPolynomial (Fin n × Fin n) ℚ,
    (k.factorial : ℚ) • rowDiv ℚ a a k (transposeVariables ℚ n f) =
      transposeVariables ℚ n ((((List.range k).map fun j : ℕ => glOps ℚ n (rowLetters n) Set.univ a a -
        (j : ℚ) • (1 : Module.End ℚ (MvPolynomial (Fin n × Fin n) ℚ))).prod) f) := by
  induction k with
  | zero =>
    intro f
    simp [qn_rowDiv_zero]
  | succ k ih =>
    intro f
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, qn_E_eq, ← ih,
      Nat.factorial_succ, Nat.cast_mul, mul_comm ((k + 1 : ℕ) : ℚ), mul_smul, qn_rowDiv_succ_diag]
end Formalism.InvariantFactorPaths.ColumnFamilies
