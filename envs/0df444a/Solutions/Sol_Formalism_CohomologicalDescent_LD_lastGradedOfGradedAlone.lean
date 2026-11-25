-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.lastGradedOfGradedAlone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:46:17.321515+00:00
-- url     : https://prove2.me/submissions/c1d0f1fe-f4c9-44b2-a6db-e89990662cc1

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_lastGradedOfGraded
import Theorems.Thm_Formalism_CohomologicalDescent_LD_expDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : LastGradedOfGradedAlone := lastGradedOfGraded expDual
end Formalism.CohomologicalDescent.LD
