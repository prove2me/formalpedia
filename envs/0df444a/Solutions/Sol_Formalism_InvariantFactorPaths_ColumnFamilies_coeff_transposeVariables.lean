-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.coeff_transposeVariables
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:03.935046+00:00
-- url     : https://prove2.me/submissions/c8cc460a-4bf8-4570-84a6-f5f72b348d24

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables

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
theorem _root_.solution (n : ℕ) (g : MvPolynomial (Fin n × Fin n) ℚ) (m : Fin n × Fin n →₀ ℕ) :
    coeff (Finsupp.mapDomain Prod.swap m) (transposeVariables ℚ n g) = coeff m g :=
  coeff_rename_mapDomain Prod.swap Prod.swap_injective g m
end Formalism.InvariantFactorPaths.ColumnFamilies
