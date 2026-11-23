-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.general_basis_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:33.224895+00:00
-- url     : https://prove2.me/submissions/32684b56-6e25-45e3-87a2-cfbb3f04fcba

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_unit_mul_X_pow
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_sum_subst_unit_mul_X_pow
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coeff_eq_zero_of_subst_sum_eq_zero

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
theorem _root_.solution : BasisGeneral := by
  intro R _ n w hn f
  have hP := hasSubst_unit_mul_X_pow n hn w
  refine ⟨fun j => PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f), eq_sum_subst_unit_mul_X_pow n hn w f, ?_⟩
  intro g' hg'
  have hg : f = ∑ j : Fin n, (g' j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) := hg'
  funext j
  ext k
  have h0 : ∑ j : Fin n, (g' j - PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst
      ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = 0 := by
    simp only [subst_sub hP, sub_mul, Finset.sum_sub_distrib]
    rw [← hg, ← eq_sum_subst_unit_mul_X_pow n hn w f, sub_self]
  have h1 := coeff_eq_zero_of_subst_sum_eq_zero n hn w k _ h0 j
  rw [map_sub, sub_eq_zero] at h1
  exact h1
end Formalism.CohomologicalDescent.HeightDescentMinors
