-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.unit_series_constant_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:43.812687+00:00
-- url     : https://prove2.me/submissions/d83692f5-0d72-4f93-9124-222c42e4dbbb

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_pi0Subst_laws_hold
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_inc_zero
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r6_holds


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
theorem _root_.solution : UnConst := by
  intro l _ O _ _ _ hl u c hu
  obtain ⟨un0, h0, he0, -, -⟩ := r6_holds l O hl u c hu
  obtain ⟨-, -, -, hX, hq, -, -, hinj⟩ := pi0Subst_laws_hold l O
  have hinj := hinj hl
  have hz : inc l O 0 = 0 := inc_zero l O
  have hpi : pi0 l O ≠ 0 := by
    rw [← hX, ← hz]
    exact fun h => X_ne_zero (hinj h)
  have hq0 : q0 l O ≠ 0 := by
    rw [← hq, ← hz]
    intro h
    have h1 := hinj h
    have h2 := congrArg (coeff 1) h1
    rw [map_sub, coeff_one_X, coeff_C, if_neg one_ne_zero, sub_zero, map_zero] at h2
    exact one_ne_zero h2
  have huniq : ∀ a b : O⟦X⟧, IsUn l O u a → IsUn l O u b → a = b := by
    intro a b ha hb
    have h1 : pi0 l O * (1 + inc l O a * q0 l O) = pi0 l O * (1 + inc l O b * q0 l O) :=
      ha.symm.trans hb
    have h2 := mul_left_cancel₀ hpi h1
    have h3 : inc l O a * q0 l O = inc l O b * q0 l O := add_left_cancel h2
    exact hinj (mul_right_cancel₀ hq0 h3)
  refine ⟨⟨un0, h0⟩, fun un hun => ⟨fun un' hun' => huniq un' un hun' hun, ?_⟩⟩
  rw [huniq un un0 hun h0]
  exact he0
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
