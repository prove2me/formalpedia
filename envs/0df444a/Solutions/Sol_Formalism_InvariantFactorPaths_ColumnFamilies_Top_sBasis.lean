-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.Top.sBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:26:48.248543+00:00
-- url     : https://prove2.me/submissions/76701855-a1e3-4033-a3fa-2fc06ccaf756

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LemmaA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ClosureBasicModules
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_InducedSectionsSpanStatement
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FinalA
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_standard_basis_theorem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies Formalism.InvariantFactorPaths.ColumnFamilies.Top
namespace Formalism.InvariantFactorPaths.ColumnFamilies.Top
theorem _root_.solution : SBasis := standard_basis_theorem
end Formalism.InvariantFactorPaths.ColumnFamilies.Top
