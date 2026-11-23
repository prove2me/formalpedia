-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.subst_zero_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:11.308826+00:00
-- url     : https://prove2.me/submissions/a842aec9-660e-42fc-a422-4cdecc5065b0

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
variable {R : Type} [CommRing R]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution {a : R⟦X⟧} (ha : HasSubst a) : (0 : R⟦X⟧).subst a = 0 := by
  rw [← PowerSeries.coe_substAlgHom ha, map_zero]
end Formalism.CohomologicalDescent.HeightDescentMinors
