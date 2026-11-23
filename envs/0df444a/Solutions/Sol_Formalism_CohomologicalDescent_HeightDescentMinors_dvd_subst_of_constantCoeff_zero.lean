-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.dvd_subst_of_constantCoeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:34:40.19924+00:00
-- url     : https://prove2.me/submissions/f42db78b-a77c-46bc-ac7b-605c67ee2b48

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_subst_self

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
theorem _root_.solution {R : Type} [CommRing R] (a f : R⟦X⟧) (ha : HasSubst a)
    (hf : constantCoeff f = 0) : a ∣ f.subst a := dvd_subst_self ha hf
end Formalism.CohomologicalDescent.HeightDescentMinors
