-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.minor_reduction_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:40:06.768971+00:00
-- url     : https://prove2.me/submissions/c11efa32-66a5-4d74-aab3-79a7b2bc7014

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
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : MinorRed := by
  intro O k _ _ red lam n t S P f g hl
  have h1 : ((P.map (PowerSeries.map red)).submatrix f g).det =
      PowerSeries.map red (P.submatrix f g).det := by
    rw [RingHom.map_det]; rfl
  refine ⟨h1, fun h => ?_⟩
  rw [h1]
  have := map_dvd (PowerSeries.map red) h
  simpa [hl] using this
end Formalism.CohomologicalDescent.HeightDescentMinors
