-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.condition_drop_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:10:27.701503+00:00
-- url     : https://prove2.me/submissions/1c7a16f0-1ffc-4395-b15c-987be94ca609

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_cond_of_euler_eigen
import Theorems.Thm_Formalism_CountingSumsFrames_pol_iff_eul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : YCondDrop := by
  intro p _ K r _ LL M hv F hF hY
  exact mem_cond_of_euler_eigen LL hv M (LL.deg (Fin.last K)) F hY ((pol_iff_eul LL F).1 hF (Fin.last K))
end Formalism.InvariantFactorPaths.L4
