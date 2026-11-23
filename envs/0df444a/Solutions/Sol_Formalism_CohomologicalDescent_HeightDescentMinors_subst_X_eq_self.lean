-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.subst_X_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:11.285796+00:00
-- url     : https://prove2.me/submissions/0c8c3324-6fd3-45ed-8b8a-18778c09447b

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
theorem _root_.solution {R : Type*} [CommRing R] (f : R⟦X⟧) : f.subst (X : R⟦X⟧) = f := PowerSeries.X_subst f
end Formalism.CohomologicalDescent.HeightDescentMinors
