-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.d_n_rank_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:26:40.457803+00:00
-- url     : https://prove2.me/submissions/aae5562f-b352-4ed0-bbc8-4931f1686016

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dn2

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
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : Dn2 := dn2
end Formalism.CohomologicalDescent.LD
