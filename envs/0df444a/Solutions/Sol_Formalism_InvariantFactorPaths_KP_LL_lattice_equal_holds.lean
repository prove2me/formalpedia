-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.lattice_equal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:57:01.581824+00:00
-- url     : https://prove2.me/submissions/e254ca0f-92d1-46f3-aa57-1a001be230d1

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_lat_tie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution : LatTie := by
  intro p _ N r _ D hB hF j jp i m L hmL x hx
  exact lat_tie hB hF j jp i m L hmL x hx
end Formalism.InvariantFactorPaths.KP.LL
