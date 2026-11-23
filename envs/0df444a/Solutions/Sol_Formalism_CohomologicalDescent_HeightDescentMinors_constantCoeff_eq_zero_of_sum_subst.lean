-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.constantCoeff_eq_zero_of_sum_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:33.898593+00:00
-- url     : https://prove2.me/submissions/97e09087-aff8-489d-899b-2a8bf93c1471

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_subst_eq_sum_range_add_pow_mul
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_unit_mul_X_pow

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
theorem _root_.solution (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (d : Fin n → R⟦X⟧)
    (h0 : ∑ j : Fin n, (d j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = 0) (i : Fin n) :
    constantCoeff (d i) = 0 := by
  have hP := hasSubst_unit_mul_X_pow n hn w
  choose h hh using fun j : Fin n => subst_eq_sum_range_add_pow_mul hP 1 (d j)
  simp only [Finset.sum_range_one, pow_zero, mul_one, pow_one,
    coeff_zero_eq_constantCoeff_apply] at hh
  have e : ∑ j : Fin n, (d j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) =
      ∑ j : Fin n, C (constantCoeff (d j)) * X ^ (j : ℕ) +
        X ^ n * ((w : R⟦X⟧) * ∑ j : Fin n, h j * X ^ (j : ℕ)) := by
    rw [Finset.sum_congr rfl fun j _ => by rw [hh j]]
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e] at h0
  have h1 := congrArg (coeff (i : ℕ)) h0
  rw [map_add, map_sum, coeff_X_pow_mul', if_neg (by have := i.2; omega), add_zero, map_zero] at h1
  simp only [coeff_C_mul_X_pow] at h1
  rw [Finset.sum_eq_single i] at h1
  · simpa using h1
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext h.symm)
  · simp
end Formalism.CohomologicalDescent.HeightDescentMinors
