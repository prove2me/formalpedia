-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.ideal_ne_top_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:51.898795+00:00
-- url     : https://prove2.me/submissions/7d690ab8-3238-4270-8a72-0baad4eb3c3d

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
variable {O : Type} [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O)
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : I ≠ ⊤ := by
  intro h
  have := IsAdicComplete.le_jacobson_bot I
  rw [h, top_le_iff, Ideal.jacobson_eq_top_iff] at this
  exact bot_ne_top this
end Formalism.CohomologicalDescent.HeightDescentMinors
