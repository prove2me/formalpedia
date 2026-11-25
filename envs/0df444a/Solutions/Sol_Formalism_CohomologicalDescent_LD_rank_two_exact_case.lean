-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.rank_two_exact_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:23:43.157849+00:00
-- url     : https://prove2.me/submissions/ba81e012-522d-414b-9c4b-9450f9ada6d0

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank2Exact

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
theorem _root_.solution : Rank2Exact := rank2Exact
end Formalism.CohomologicalDescent.LD
