-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.map_pi0_padicInt_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:52.949886+00:00
-- url     : https://prove2.me/submissions/15b066d5-4027-4fe3-8c6b-4bc22e320497

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_pi0_padic

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
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : PowerSeries.map (algebraMap ℤ_[l] O) (pi0 l ℤ_[l]) = pi0 l O := map_pi0_padic l O
end Formalism.CohomologicalDescent.HeightDescentMinors
