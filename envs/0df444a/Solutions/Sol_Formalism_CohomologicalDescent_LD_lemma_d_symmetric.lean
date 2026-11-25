-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.lemma_d_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:15:22.248784+00:00
-- url     : https://prove2.me/submissions/6fa217cf-c5cb-4c7d-9ded-f02bf5118a09

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_lemmaD_sym

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
theorem _root_.solution : LemmaD_sym := lemmaD_sym
end Formalism.CohomologicalDescent.LD
