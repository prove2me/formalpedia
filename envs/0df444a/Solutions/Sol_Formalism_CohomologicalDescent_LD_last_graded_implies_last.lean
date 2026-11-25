-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.last_graded_implies_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:16:51.5983+00:00
-- url     : https://prove2.me/submissions/4709d1f0-00b4-4fee-a0eb-d8d5a4dfe440

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_lastGradedImpliesLast

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
theorem _root_.solution : LastGradedImpliesLast := lastGradedImpliesLast
end Formalism.CohomologicalDescent.LD
