-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.cancel_unit_mul_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:07.682862+00:00
-- url     : https://prove2.me/submissions/469af9c9-fb84-4ae9-a14e-a68bd528bb2b

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
theorem _root_.solution (n : ℕ) (w : (R⟦X⟧)ˣ) {a b : R⟦X⟧}
    (h : (w : R⟦X⟧) * X ^ n * a = (w : R⟦X⟧) * X ^ n * b) : a = b := by
  have h' : X ^ n * a = X ^ n * b := by
    have := congrArg (fun t => ((w⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) * t) h
    simp only [← mul_assoc, Units.inv_mul, one_mul] at this
    exact this
  ext k
  have := congrArg (coeff (k + n)) h'
  simpa [PowerSeries.coeff_X_pow_mul'] using this
end Formalism.CohomologicalDescent.HeightDescentMinors
