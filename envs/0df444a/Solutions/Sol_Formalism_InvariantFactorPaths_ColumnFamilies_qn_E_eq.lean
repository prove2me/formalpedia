-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_E_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:22.344071+00:00
-- url     : https://prove2.me/submissions/c5a70b36-f54f-4bb2-a57c-f859d0b9f8e9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_D_apply
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
theorem _root_.solution (n : ℕ) (a b : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    glOps ℚ n (rowLetters n) Set.univ a b f = qn_D n a b f := by
  rw [qn_D_apply]
  simp [glOps, glAct, rowLetters, LinearMap.sum_apply]
end Formalism.InvariantFactorPaths.ColumnFamilies
