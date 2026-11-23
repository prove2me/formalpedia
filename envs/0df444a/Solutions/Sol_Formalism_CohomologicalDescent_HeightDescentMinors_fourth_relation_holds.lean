-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.fourth_relation_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:37.583884+00:00
-- url     : https://prove2.me/submissions/61a7c1c5-c1d8-4dd5-92fc-f0114f8ef714

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_fourth_relation_of_unit_and_basis
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r2_basis_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r3_unit_holds

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
theorem _root_.solution : R4 := fourth_relation_of_unit_and_basis r3_unit_holds r2_basis_holds
end Formalism.CohomologicalDescent.HeightDescentMinors
