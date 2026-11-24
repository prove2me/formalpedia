-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.Top.closure_first_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:42.59379+00:00
-- url     : https://prove2.me/submissions/54647a37-f85c-4745-87dc-2b5969fdfaad

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LemmaA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ClosureBasicModules
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_InducedSectionsSpanStatement
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FinalA
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_claimA_straightening
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_closure_first_part_of
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
theorem _root_.solution : ClosureBasicModules := closure_first_part_of claimA_straightening standard_basis_theorem
end Formalism.InvariantFactorPaths.ColumnFamilies.Top
