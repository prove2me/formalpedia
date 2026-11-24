-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.rank_two_vector_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:43:40.760393+00:00
-- url     : https://prove2.me/submissions/24e22b1b-5dab-419a-b476-950bba807498

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector

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
theorem _root_.solution (w y i : ℕ) : vec2 w y i = X (0, 0) ^ (w - y - i) * X (1, 0) ^ i * ldDet ^ y := rfl
end Formalism.CohomologicalDescent.LD
