-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.coeff_eq_zero_of_subst_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:27.621671+00:00
-- url     : https://prove2.me/submissions/2539946c-75a3-4993-93f6-80a0fd006f8a

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coeff_subst_X_mul_of_low_zero

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
theorem _root_.solution (s f : R⟦X⟧) (n : ℕ) (hinv : f.subst (X * s) = f)
    (hu : ∀ j, 0 < j → j < n → IsUnit (constantCoeff s ^ j - 1)) :
    ∀ j, 0 < j → j < n → coeff j f = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h0 hn
    have h1 := coeff_subst_X_mul_of_low_zero s f j h0 (fun i hi hij => ih i hij hi (by omega))
    rw [hinv] at h1
    have h2 : coeff j f * (constantCoeff s ^ j - 1) = 0 := by linear_combination -h1
    exact (hu j h0 hn).mul_left_eq_zero.mp h2
end Formalism.CohomologicalDescent.HeightDescentMinors
