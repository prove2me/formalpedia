-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.depth_two_duality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:26:44.207964+00:00
-- url     : https://prove2.me/submissions/5217f9e7-9528-4493-8f56-1776e0a2ef1f

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_depth2Dual

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
theorem _root_.solution : Depth2Dual := depth2Dual
end Formalism.CohomologicalDescent.LD
