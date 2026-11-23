-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.r3_unit_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:15.623876+00:00
-- url     : https://prove2.me/submissions/102f1039-393b-4d91-ba0a-8dc1d921eb5f

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_action_laws_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_q_multiplicative_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_mu_facts_hold
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r3_unit_of_laws

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
theorem _root_.solution : UnitFactorQ := r3_unit_of_laws action_laws_holds mu_facts_hold q_multiplicative_holds
end Formalism.CohomologicalDescent.HeightDescentMinors
