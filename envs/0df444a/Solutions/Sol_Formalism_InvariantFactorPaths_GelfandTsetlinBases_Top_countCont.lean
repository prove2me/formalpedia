-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.countCont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:11:24.93054+00:00
-- url     : https://prove2.me/submissions/c0915b07-002e-44c7-9bfa-695b1d29fc8e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_FinalP
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Top_stripsMem
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Top_gtPieri
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Top_stdCountGT
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_countCont_of


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
theorem _root_.solution : CountCont := countCont_of stripsMem gtPieri stdCountGT
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
