-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.r5_character_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:40:09.944189+00:00
-- url     : https://prove2.me/submissions/e946ddbb-8dce-45cb-af98-9dce8c55f6d6

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_one_add_X_pow_sub_one_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_X_pow_of_ne_zero
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_pi0_eq_zero
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_pi0_relation_holds

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
theorem _root_.solution : FrobeniusCharP := by
  intro l _ O _ _ _ g
  obtain ⟨r, hr⟩ := pi0_relation_holds l O
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have h0 : (l : O) = 0 := CharP.cast_eq_zero O l
  have hp : HasSubst (pi0 l O) := HasSubst.of_constantCoeff_zero' (constantCoeff_pi0_eq_zero l O)
  have ha : HasSubst ((1 + X) ^ l - 1 : O⟦X⟧) := hasSubst_one_add_X_pow_sub_one_alt l
  have hX : HasSubst (X ^ l : O⟦X⟧) := hasSubst_X_pow_of_ne_zero hl
  have h1 : (pi0 l O).subst ((1 + X) ^ l - 1 : O⟦X⟧) = pi0 l O ^ l := by
    have h2 := hr
    unfold phi at h2
    rw [h2, h0]
    simp
  unfold inc phi
  rw [subst_comp_subst_apply hp ha, subst_comp_subst_apply hX hp, subst_pow hp, subst_X hp, h1]
end Formalism.CohomologicalDescent.HeightDescentMinors
