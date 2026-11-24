-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.map_binomialSeriesSubOne_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:40:03.506405+00:00
-- url     : https://prove2.me/submissions/b76d7454-153d-466c-8ace-651309200659

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
theorem _root_.solution (c : ℤ_[l]) :
    PowerSeries.map (algebraMap ℤ_[l] O) (br l ℤ_[l] c) = br l O c := map_algebraMap_binomialSeriesSubOne l O c
end Formalism.CohomologicalDescent.HeightDescentMinors
