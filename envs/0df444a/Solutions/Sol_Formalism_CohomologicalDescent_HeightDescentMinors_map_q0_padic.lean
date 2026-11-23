-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.map_q0_padic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:53.432829+00:00
-- url     : https://prove2.me/submissions/e5cbc474-1161-448e-97c1-b6cdf22e0f17

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_q0_padicInt

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
theorem _root_.solution : PowerSeries.map (algebraMap ℤ_[l] O) (q0 l ℤ_[l]) = q0 l O := map_q0_padicInt l O
end Formalism.CohomologicalDescent.HeightDescentMinors
