-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.pi0Subst_laws_hold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:14:42.911991+00:00
-- url     : https://prove2.me/submissions/d7d2745f-2aef-42f3-8147-5fd4c3b48e05

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_subst_C_eq_C
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_constantCoeff_subst_of_constantCoeff_zero_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_pi0
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_pi0_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_inc_X_sub_l_eq_q0
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_inc_zero
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prime_sub_one_pos_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r2_basis_holds


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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : IncLaws := by
  intro l _ O _ _
  have hP := hasSubst_pi0_alt l O
  have hc := constantCoeff_pi0 l O
  refine ⟨fun f g => subst_add hP f g, fun f g => subst_mul hP f g, fun a => subst_C_eq_C a,
    subst_X hP, inc_X_sub_l_eq_q0 l O, fun f => constantCoeff_subst_of_constantCoeff_zero_alt hc f, ?_, ?_⟩
  · intro f p hp
    have hp' : HasSubst p := HasSubst.of_constantCoeff_zero' hp
    exact subst_comp_subst_apply hp' hP f
  · intro h2 f g hfg
    obtain ⟨g0, -, hu⟩ := r2_basis_holds l O h2 (inc l O f)
    have hpos := prime_sub_one_pos_alt l
    let j0 : Fin (l - 1) := ⟨0, hpos⟩
    have key : ∀ y : O⟦X⟧, inc l O y = inc l O f →
        (fun j : Fin (l - 1) => if j = j0 then y else 0) = g0 := by
      intro y hy
      refine hu _ ?_
      show inc l O f = ∑ j : Fin (l - 1), inc l O (if j = j0 then y else 0) * X ^ (j : ℕ)
      rw [Finset.sum_eq_single j0]
      · simp [j0, hy]
      · intro j _ hj
        simp [hj, inc_zero]
      · intro hj
        exact absurd (Finset.mem_univ _) hj
    have h1 := key f rfl
    have h2' := key g hfg.symm
    have h3 := congrFun (h1.trans h2'.symm) j0
    simpa using h3
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
