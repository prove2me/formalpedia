-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_mem_weightSp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:04.438961+00:00
-- url     : https://prove2.me/submissions/6da627c9-b2e4-4fc4-bb0e-3db6d62cbf53

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
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
theorem _root_.solution (n : ℕ) (w : Fin n → ℤ) (z : MvPolynomial (Fin n × Fin n) ℚ) :
    z ∈ weightSp (glOps ℚ n (rowLetters n) Set.univ) w ↔
      ∀ a, glOps ℚ n (rowLetters n) Set.univ a a z = (w a : ℚ) • z := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]
end Formalism.InvariantFactorPaths.ColumnFamilies
