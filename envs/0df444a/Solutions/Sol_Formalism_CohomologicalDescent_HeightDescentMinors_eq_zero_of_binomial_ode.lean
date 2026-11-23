-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.eq_zero_of_binomial_ode
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:34:54.319826+00:00
-- url     : https://prove2.me/submissions/e489c397-8bdc-4ccd-af36-221da3a5bfb6

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coeff_one_add_X_mul_derivative

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
theorem _root_.solution [IsAddTorsionFree R] (c : R) (H : R⟦X⟧)
    (h : (1 + X) * d⁄dX R H = C c * H) (h0 : constantCoeff H = 0) : H = 0 := by
  ext n
  simp only [map_zero]
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have e := congrArg (coeff n) h
    rw [coeff_one_add_X_mul_derivative, PowerSeries.coeff_C_mul] at e
    simp only [ih, zero_mul, mul_zero, add_zero] at e
    have e2 : (n + 1) • coeff (n + 1) H = 0 := by
      rw [nsmul_eq_mul, mul_comm]
      push_cast
      exact e
    exact nsmul_right_injective (Nat.succ_ne_zero n) (by simpa using e2)
end Formalism.CohomologicalDescent.HeightDescentMinors
