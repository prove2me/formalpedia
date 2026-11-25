-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.application_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:16:53.67264+00:00
-- url     : https://prove2.me/submissions/c565fe15-370c-473f-aae4-4cf5fc9d9bcb

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_applicationSteps

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
theorem _root_.solution : ApplicationSteps := applicationSteps
end Formalism.CohomologicalDescent.LD
