-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.fixed_relation_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:21.075324+00:00
-- url     : https://prove2.me/submissions/9bcdd96d-ed38-444c-8177-04c6f269a3d1

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_mu_facts_hold
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r1_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r2_inverse_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_fixed_relation_of_mu_and_inverse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : RootsOfUnityInvariants := fixed_relation_of_mu_and_inverse mu_facts_hold r1_holds r2_inverse_holds
end Formalism.CohomologicalDescent.HeightDescentMinors
