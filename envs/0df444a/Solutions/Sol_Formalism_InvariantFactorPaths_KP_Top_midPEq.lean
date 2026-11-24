-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.Top.midPEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:48:33.706232+00:00
-- url     : https://prove2.me/submissions/0406564e-1b1a-4e73-8b58-995c4ca10235

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PstScalMem
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepPlus
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LevelLatticeOf
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_FinalLL
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_middle_p_eq_holds


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
theorem _root_.solution : MidPEq := middle_p_eq_holds
end Formalism.InvariantFactorPaths.KP.Top
