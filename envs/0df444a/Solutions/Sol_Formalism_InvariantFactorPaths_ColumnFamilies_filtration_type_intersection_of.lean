-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.filtration_type_intersection_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:32:21.9148+00:00
-- url     : https://prove2.me/submissions/53aa546f-7b94-4c3e-b72f-94b3beca5867

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_filtration_type_intersection_ofA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : LemmaA → SBasis → FiltrationTypeIntersection := fun hA _ => filtration_type_intersection_ofA hA
end Formalism.InvariantFactorPaths.ColumnFamilies
