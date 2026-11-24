-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.Top.plLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:41:47.671809+00:00
-- url     : https://prove2.me/submissions/04466afe-2ab5-4004-b7de-02502717ceac

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PstScalMem
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepPlus
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LevelLatticeOf
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_FinalLL
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_lattice_linear_holds


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
theorem _root_.solution : PLLin := lattice_linear_holds
end Formalism.InvariantFactorPaths.KP.Top
