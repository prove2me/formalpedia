-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.last_graded_implies_one_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:16:53.507498+00:00
-- url     : https://prove2.me/submissions/0185341e-4f77-4841-a87f-973d38a5c113

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LD_last_graded_implies_one_block__d071e15f0234

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
theorem _root_.solution : OneRowBoundOfLastGraded := last_graded_implies_one_block'
end Formalism.CohomologicalDescent.LD
