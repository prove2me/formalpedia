-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.exists_subst_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:32.543646+00:00
-- url     : https://prove2.me/submissions/7aadc35a-0146-4cef-b25b-c44bf429ff9f

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_subst_zero_eq_zero
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_unit_mul_X_pow
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_sum_subst_unit_mul_X_pow
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coeff_eq_zero_of_subst_invariant
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_averagedSeries_subst_invariant

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
theorem _root_.solution (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (s f : R⟦X⟧)
    (hP : ((w : R⟦X⟧) * X ^ n).subst (X * s) = (w : R⟦X⟧) * X ^ n)
    (hinv : f.subst (X * s) = f)
    (hu : ∀ j, 0 < j → j < n → IsUnit (constantCoeff s ^ j - 1)) :
    ∃ g : R⟦X⟧, f = g.subst ((w : R⟦X⟧) * X ^ n) := by
  have hit : ∀ k, ((divQuotient n w)^[k] f).subst (X * s) = (divQuotient n w)^[k] f := by
    intro k
    induction k with
    | zero => simpa using hinv
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact averagedSeries_subst_invariant n hn w s _ hP ih hu
  refine ⟨PowerSeries.mk fun k => coeff 0 ((divQuotient n w)^[k] f), ?_⟩
  have h := eq_sum_subst_unit_mul_X_pow n hn w f
  have h' : ∑ j : Fin n, (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst
          ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) =
      (PowerSeries.mk fun k => coeff 0 ((divQuotient n w)^[k] f)).subst ((w : R⟦X⟧) * X ^ n) := by
    rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · rw [pow_zero, mul_one]
    · intro b _ hb
      have hz : (PowerSeries.mk fun k => coeff (b : ℕ) ((divQuotient n w)^[k] f)) = 0 := by
        ext k
        rw [coeff_mk, map_zero]
        exact coeff_eq_zero_of_subst_invariant s _ n (hit k) hu b
          (Nat.pos_of_ne_zero fun h => hb (Fin.ext h)) b.2
      rw [hz, subst_zero_eq_zero (hasSubst_unit_mul_X_pow n hn w), zero_mul]
    · simp
  exact h.trans h'
end Formalism.CohomologicalDescent.HeightDescentMinors
