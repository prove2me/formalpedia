-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_T_divPowE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:39.784106+00:00
-- url     : https://prove2.me/submissions/e5df8df0-8368-4e38-8919-011b07a6b867

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_fact_rowDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    transposeVariables ℚ n (divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k f) = rowDiv ℚ a b k (transposeVariables ℚ n f) := by
  have hk : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  rw [divPowE, LinearMap.smul_apply, map_smul, ← qn_fact_rowDiv n a b hab k f, smul_smul,
    inv_mul_cancel₀ hk, one_smul]
end Formalism.InvariantFactorPaths.ColumnFamilies
