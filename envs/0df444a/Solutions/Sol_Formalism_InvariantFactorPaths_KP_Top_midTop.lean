-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.Top.midTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:56:15.732867+00:00
-- url     : https://prove2.me/submissions/d5fb4c48-fe39-4065-ad84-a09bf759e1d2

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PstScalMem
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepPlus
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LevelLatticeOf
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_FinalLL
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_middle_top_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.Top
open Formalism.InvariantFactorPaths.KP.LL
namespace Formalism.InvariantFactorPaths.KP.Top
theorem _root_.solution : MidTop := middle_top_holds
end Formalism.InvariantFactorPaths.KP.Top
