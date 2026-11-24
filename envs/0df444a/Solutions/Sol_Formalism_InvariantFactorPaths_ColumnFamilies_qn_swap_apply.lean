-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_swap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:18.424517+00:00
-- url     : https://prove2.me/submissions/a98109e4-a55f-4b7d-b416-ce72d5ae40cc

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
theorem _root_.solution {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a l : Fin n) :
    (Finsupp.mapDomain Prod.swap m) (a, l) = m (l, a) :=
  Finsupp.mapDomain_apply Prod.swap_injective m (l, a)
end Formalism.InvariantFactorPaths.ColumnFamilies
