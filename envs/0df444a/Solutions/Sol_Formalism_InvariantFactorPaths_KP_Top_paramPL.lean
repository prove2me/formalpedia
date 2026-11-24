-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.Top.paramPL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:41:40.789085+00:00
-- url     : https://prove2.me/submissions/668ba626-08d4-4835-9aa8-38d152bf5075

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PstScalMem
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepPlus
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LevelLatticeOf
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_FinalLL
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_param_lattice_holds


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
theorem _root_.solution : ParamPL := param_lattice_holds
end Formalism.InvariantFactorPaths.KP.Top
