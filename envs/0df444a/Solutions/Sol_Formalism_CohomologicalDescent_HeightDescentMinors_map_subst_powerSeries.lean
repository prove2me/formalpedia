-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.map_subst_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:30:10.682029+00:00
-- url     : https://prove2.me/submissions/df6719fc-9d50-4ed3-af6c-d7d2153ac8dc

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
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {a : R⟦X⟧}
    (ha : HasSubst a) (f : R⟦X⟧) :
    PowerSeries.map h (f.subst a) = (PowerSeries.map h f).subst (PowerSeries.map h a) := by
  first
    | exact PowerSeries.map_subst ha f
    | exact PowerSeries.map_subst ha h f
    | exact PowerSeries.map_subst (R := R) (S := S) ha (h := h) f
    | exact (PowerSeries.map_subst ha).symm
end Formalism.CohomologicalDescent.HeightDescentMinors
