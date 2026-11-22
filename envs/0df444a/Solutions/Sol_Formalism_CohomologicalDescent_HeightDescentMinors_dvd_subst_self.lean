-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.dvd_subst_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:34.248524+00:00
-- url     : https://prove2.me/submissions/201a9f65-1e6e-4045-a6f1-380d8f73328c

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
theorem _root_.solution {R : Type} [CommRing R] {a f : R⟦X⟧} (ha : HasSubst a)
    (hf : constantCoeff f = 0) : a ∣ f.subst a := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]
  exact dvd_mul_right _ _
end Formalism.CohomologicalDescent.HeightDescentMinors
