-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.r2_basis_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:57.648948+00:00
-- url     : https://prove2.me/submissions/7516fbaf-c28d-4c8a-91b9-237102c0da1d

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r1_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_general_basis_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r2_basis_of_r1

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
theorem _root_.solution : PowerSeriesFreeBasis := r2_basis_of_r1 r1_holds general_basis_holds
end Formalism.CohomologicalDescent.HeightDescentMinors
