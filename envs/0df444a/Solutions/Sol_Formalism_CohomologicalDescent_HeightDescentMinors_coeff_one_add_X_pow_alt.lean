-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.coeff_one_add_X_pow_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:20.305852+00:00
-- url     : https://prove2.me/submissions/add816ca-baa0-41eb-8088-3ba19a763739

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
theorem _root_.solution (R : Type*) [CommRing R] (d n : ℕ) :
    coeff n ((1 + X : R⟦X⟧) ^ d) = (d.choose n : R) := by
  have e : ((1 + X : R⟦X⟧)) ^ d = (((1 + Polynomial.X) ^ d : Polynomial R) : R⟦X⟧) := by
    simp [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [e, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
end Formalism.CohomologicalDescent.HeightDescentMinors
