-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.map_q_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:01.278024+00:00
-- url     : https://prove2.me/submissions/0be232b6-1edc-4a66-9712-306f6c019ebb

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

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
theorem _root_.solution : PowerSeries.map (algebraMap ℤ_[l] O) (q l ℤ_[l]) = q l O := by
  ext j
  simp [q]
end Formalism.CohomologicalDescent.HeightDescentMinors
