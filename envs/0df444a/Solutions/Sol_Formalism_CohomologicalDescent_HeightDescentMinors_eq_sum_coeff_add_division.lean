-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.eq_sum_coeff_add_division
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:34.268818+00:00
-- url     : https://prove2.me/submissions/ee3eca07-13e7-45f7-92a8-8dac859a0638

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
theorem _root_.solution (n : ℕ) (w : (R⟦X⟧)ˣ) (f : R⟦X⟧) :
    f = ∑ j : Fin n, C (coeff (j : ℕ) f) * X ^ (j : ℕ) + (w : R⟦X⟧) * X ^ n * divQuotient n w f := by
  have e : (w : R⟦X⟧) * X ^ n * divQuotient n w f = X ^ n * PowerSeries.mk fun i => coeff (i + n) f := by
    unfold divQuotient
    calc (w : R⟦X⟧) * X ^ n * (((w⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) * PowerSeries.mk fun i => coeff (i + n) f)
        = ((w : R⟦X⟧) * ((w⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧)) * (X ^ n * PowerSeries.mk fun i => coeff (i + n) f) := by
          ring
      _ = X ^ n * PowerSeries.mk fun i => coeff (i + n) f := by rw [Units.mul_inv, one_mul]
  rw [e]
  ext m
  rw [map_add, map_sum, coeff_X_pow_mul']
  simp only [coeff_C_mul_X_pow, coeff_mk]
  by_cases hm : m < n
  · rw [if_neg (by omega), add_zero, Finset.sum_eq_single (⟨m, hm⟩ : Fin n)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext h.symm)
    · simp
  · rw [if_pos (by omega), Finset.sum_eq_zero, zero_add]
    · rw [Nat.sub_add_cancel (Nat.le_of_not_lt hm)]
    · intro b _
      rw [if_neg]
      have := b.2
      omega
end Formalism.CohomologicalDescent.HeightDescentMinors
