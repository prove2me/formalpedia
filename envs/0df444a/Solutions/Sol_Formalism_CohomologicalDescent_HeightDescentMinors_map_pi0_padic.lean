-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.map_pi0_padic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:02.84645+00:00
-- url     : https://prove2.me/submissions/7bc02617-4efa-4adc-ba7d-dbf0f9b49946

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_algebraMap_binomialSeriesSubOne

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
theorem _root_.solution : PowerSeries.map (algebraMap ℤ_[l] O) (pi0 l ℤ_[l]) = pi0 l O := by
  simp only [pi0, map_prod, map_algebraMap_binomialSeriesSubOne]
end Formalism.CohomologicalDescent.HeightDescentMinors
