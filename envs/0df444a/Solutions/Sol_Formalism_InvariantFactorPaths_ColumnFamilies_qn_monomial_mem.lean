-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_monomial_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:50.84499+00:00
-- url     : https://prove2.me/submissions/cb47dc60-badc-4bbd-bb08-4820223eae60

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_coeff_E
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_mem_weightSp
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
theorem _root_.solution (n : ℕ) (m : Fin n × Fin n →₀ ℕ) (c : ℚ) :
    monomial m c ∈ weightSp (glOps ℚ n (rowLetters n) Set.univ) (qn_wt m) := by
  classical
  rw [qn_mem_weightSp]
  intro a
  ext m'
  rw [qn_coeff_E, coeff_smul, coeff_monomial, smul_eq_mul]
  split_ifs with h
  · rw [h]
  · simp
end Formalism.InvariantFactorPaths.ColumnFamilies
