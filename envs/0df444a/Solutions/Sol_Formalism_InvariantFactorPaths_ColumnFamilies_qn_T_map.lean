-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_T_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:27.149831+00:00
-- url     : https://prove2.me/submissions/215e5954-4f20-4f96-a796-d3ad48a2a9fa

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
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
theorem _root_.solution (n : ℕ) (f : MvPolynomial (Fin n × Fin n) ℤ) :
    transposeVariables ℚ n (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℚ) (transposeVariables ℤ n f) := by
  simp only [transposeVariables]
  exact (MvPolynomial.map_rename _ _ _).symm
end Formalism.InvariantFactorPaths.ColumnFamilies
