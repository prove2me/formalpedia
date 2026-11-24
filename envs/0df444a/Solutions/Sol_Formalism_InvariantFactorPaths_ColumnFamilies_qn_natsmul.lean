-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_natsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:39.207971+00:00
-- url     : https://prove2.me/submissions/82a67ead-a1bf-4c7f-8286-948543582c8c

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
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
theorem _root_.solution (n : ℕ) (k : ℕ) (p : MvPolynomial (Fin n × Fin n) ℚ) :
    p * ((k : MvPolynomial (Fin n × Fin n) ℚ) + 1) = ((k + 1 : ℕ) : ℚ) • p := by
  rw [MvPolynomial.smul_eq_C_mul, mul_comm]
  congr 1
  simp
end Formalism.InvariantFactorPaths.ColumnFamilies
