-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.eq_sum_iterated_division
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:34:40.68071+00:00
-- url     : https://prove2.me/submissions/6ddaac61-3671-4210-be19-401c61758c93

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_sum_coeff_add_division

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
theorem _root_.solution (n : ℕ) (w : (R⟦X⟧)ˣ) (f : R⟦X⟧) (K : ℕ) :
    f = ∑ k ∈ range K, ((w : R⟦X⟧) * X ^ n) ^ k *
          (∑ j : Fin n, C (coeff (j : ℕ) ((divQuotient n w)^[k] f)) * X ^ (j : ℕ)) +
        ((w : R⟦X⟧) * X ^ n) ^ K * (divQuotient n w)^[K] f := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, Function.iterate_succ_apply']
    have h := eq_sum_coeff_add_division n w ((divQuotient n w)^[K] f)
    linear_combination ih + ((w : R⟦X⟧) * X ^ n) ^ K * h
end Formalism.CohomologicalDescent.HeightDescentMinors
