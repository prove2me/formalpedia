-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.eq_sum_subst_unit_mul_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:48.858876+00:00
-- url     : https://prove2.me/submissions/79bc5718-ed5f-4dbe-8a59-5da760adbffc

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_subst_eq_sum_range_add_pow_mul
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_unit_mul_X_pow
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_sum_iterated_division

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
theorem _root_.solution (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (f : R⟦X⟧) :
    f = ∑ j : Fin n, (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst
          ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) := by
  have hP := hasSubst_unit_mul_X_pow n hn w
  rw [← sub_eq_zero]
  ext N
  rw [map_zero]
  refine (X_pow_dvd_iff.mp ?_) N (Nat.lt_succ_self N)
  choose h hh using fun j : Fin n =>
    subst_eq_sum_range_add_pow_mul hP (N + 1) (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f))
  simp only [coeff_mk] at hh
  have e2 : ∑ j : Fin n, (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst
          ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) =
      ∑ k ∈ range (N + 1), ((w : R⟦X⟧) * X ^ n) ^ k *
          (∑ j : Fin n, C (coeff (j : ℕ) ((divQuotient n w)^[k] f)) * X ^ (j : ℕ)) +
        ((w : R⟦X⟧) * X ^ n) ^ (N + 1) * ∑ j : Fin n, h j * X ^ (j : ℕ) := by
    rw [Finset.sum_congr rfl fun j _ => by rw [hh j]]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : f - ∑ j : Fin n, (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst
          ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) =
      ((w : R⟦X⟧) * X ^ n) ^ (N + 1) *
        ((divQuotient n w)^[N + 1] f - ∑ j : Fin n, h j * X ^ (j : ℕ)) := by
    rw [e2]
    linear_combination eq_sum_iterated_division n w f (N + 1)
  rw [e3, mul_pow, ← pow_mul]
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ ?_) _) _
  exact Nat.le_mul_of_pos_left _ hn
end Formalism.CohomologicalDescent.HeightDescentMinors
