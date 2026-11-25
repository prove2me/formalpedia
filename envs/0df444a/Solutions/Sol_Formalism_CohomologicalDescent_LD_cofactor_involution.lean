-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.cofactor_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:16:57.961946+00:00
-- url     : https://prove2.me/submissions/a7723496-0733-4207-bd50-f7891f946cb5

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofCof

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
theorem _root_.solution : CofCof := cofCof
end Formalism.CohomologicalDescent.LD
