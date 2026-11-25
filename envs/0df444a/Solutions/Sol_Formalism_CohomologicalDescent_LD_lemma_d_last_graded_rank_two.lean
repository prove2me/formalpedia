-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.lemma_d_last_graded_rank_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:46:48.481563+00:00
-- url     : https://prove2.me/submissions/1784fe95-3c2e-4e68-b05b-81528aa5894e

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_lemmaDLastGraded_rank2

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
theorem _root_.solution : LemmaDLastGraded_rank2 := lemmaDLastGraded_rank2
end Formalism.CohomologicalDescent.LD
