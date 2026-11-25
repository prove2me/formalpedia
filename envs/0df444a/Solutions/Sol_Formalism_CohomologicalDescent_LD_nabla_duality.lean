-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.nabla_duality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:37:26.784771+00:00
-- url     : https://prove2.me/submissions/e0c2b6ba-9b1d-4c57-ae0e-2e4cd19fa65c

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_nablaDual

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
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : NablaDual := nablaDual
end Formalism.CohomologicalDescent.LD
