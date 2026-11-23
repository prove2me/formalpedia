-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.averagedSeries_subst_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:47.476805+00:00
-- url     : https://prove2.me/submissions/6fc2be01-b501-4e16-b49b-8eb03829d86a

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_cancel_unit_mul_X_pow
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_sum_coeff_add_division
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coeff_eq_zero_of_subst_invariant

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
    (divQuotient n w f).subst (X * s) = divQuotient n w f := by
  have ha : HasSubst (X * s) := HasSubst.of_constantCoeff_zero' (by simp)
  have hc := coeff_eq_zero_of_subst_invariant s f n hinv hu
  have hdiv := eq_sum_coeff_add_division n w f
  have hT : ∑ j : Fin n, C (coeff (j : ℕ) f) * X ^ (j : ℕ) = C (constantCoeff f) := by
    rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · simp
    · intro b _ hb
      rw [hc b (Nat.pos_of_ne_zero fun h => hb (Fin.ext h)) b.2]
      simp
    · simp
  rw [hT] at hdiv
  have h1 : f.subst (X * s) =
      C (constantCoeff f) + (w : R⟦X⟧) * X ^ n * (divQuotient n w f).subst (X * s) := by
    conv_lhs => rw [hdiv]
    rw [subst_add ha, subst_mul ha, hP, subst_C]
    rfl
  rw [hinv] at h1
  apply cancel_unit_mul_X_pow n w
  linear_combination hdiv - h1
end Formalism.CohomologicalDescent.HeightDescentMinors
