-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.countPAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:28:10.13371+00:00
-- url     : https://prove2.me/submissions/e99245b0-6252-45ac-8774-1086211aeca5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_FinalP
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Top_countCont
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_countPAll_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
open Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
theorem _root_.solution : CountPAll := countPAll_of countCont
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
