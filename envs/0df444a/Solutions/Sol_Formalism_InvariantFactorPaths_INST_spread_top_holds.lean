-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.spread_top_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:48:32.863658+00:00
-- url     : https://prove2.me/submissions/dd90506d-1cbd-4272-b683-abf5faec2c54

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Spread
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_spr_upper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution : SpreadTop := by
  intro R _ _ r n ν l hl f hf g _ m hm m' _ a
  exact (spr_upper R r n ν l hl f hf m hm a).trans (Nat.le_add_left _ _)
end Formalism.InvariantFactorPaths.INST
