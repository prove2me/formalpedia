-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.Top.lemmaA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:49:40.270982+00:00
-- url     : https://prove2.me/submissions/5947c26d-030b-4869-b13b-a607e5bba9fa

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LemmaA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ClosureBasicModules
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_InducedSectionsSpanStatement
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FinalA
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_claimA_straightening


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
theorem _root_.solution : LemmaA := claimA_straightening
end Formalism.InvariantFactorPaths.ColumnFamilies.Top
