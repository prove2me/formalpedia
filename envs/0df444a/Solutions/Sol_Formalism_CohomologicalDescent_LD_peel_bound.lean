-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.peel_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:05:32.31058+00:00
-- url     : https://prove2.me/submissions/d887e41f-6c6e-4bf0-9af8-1dcdc2a2fe78

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_peelBound

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
theorem _root_.solution : PeelBound := peelBound
end Formalism.CohomologicalDescent.LD
