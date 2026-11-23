-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.eq_of_binomial_ode_of_constantCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:35.799796+00:00
-- url     : https://prove2.me/submissions/4d3e3844-7769-4d66-86c3-109c9a055d83

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_zero_of_binomial_ode

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
variable {R : Type*} [CommRing R]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution [IsAddTorsionFree R] (c : R) (F G : R⟦X⟧)
    (hF : (1 + X) * d⁄dX R F = C c * F) (hG : (1 + X) * d⁄dX R G = C c * G)
    (h0 : constantCoeff F = constantCoeff G) : F = G := by
  have := eq_zero_of_binomial_ode c (F - G) (by rw [map_sub, mul_sub, hF, hG, mul_sub])
    (by rw [map_sub, h0, sub_self])
  exact sub_eq_zero.mp this
end Formalism.CohomologicalDescent.HeightDescentMinors
