-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.expDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:22:28.266539+00:00
-- url     : https://prove2.me/submissions/cf6bac61-88ea-4714-adb9-7f5203d4df6a

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_nablaDual
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dualWeight
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofCof
import Theorems.Thm_Formalism_CohomologicalDescent_LD_weylDual
import Theorems.Thm_Formalism_CohomologicalDescent_LD_expDualOfLattices

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
theorem _root_.solution : ExpDual := expDualOfLattices nablaDual weylDual dualWeight cofCof
end Formalism.CohomologicalDescent.LD
