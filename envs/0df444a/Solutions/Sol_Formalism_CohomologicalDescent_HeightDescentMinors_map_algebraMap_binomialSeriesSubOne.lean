-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.map_algebraMap_binomialSeriesSubOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:53.390861+00:00
-- url     : https://prove2.me/submissions/3bb17ab5-e4ae-4733-925c-52bd076e746d

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_binomialSeries_alt

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
theorem _root_.solution (c : ℤ_[l]) :
    PowerSeries.map (algebraMap ℤ_[l] O) (br l ℤ_[l] c) = br l O c := by
  simp only [br, map_sub, map_one, map_binomialSeries_alt]
end Formalism.CohomologicalDescent.HeightDescentMinors
