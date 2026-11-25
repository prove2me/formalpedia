-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.frobenius_on_pi0Subst_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:54:38.820275+00:00
-- url     : https://prove2.me/submissions/54a03cc6-7ba1-40f9-a21d-1b5ab52cc978

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_pi0Subst_laws_hold
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_pi0Subst_reduction_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_action_laws_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_fixed_relation_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r5_character_holds


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
theorem _root_.solution : PhiOnInc := by
  intro l _ O k _ _ _ _ _ red hl hred y
  obtain ⟨-, -, -, -, hcomm, -, -⟩ := action_laws_holds l O
  refine ⟨?_, ?_⟩
  · refine (fixed_relation_holds l O hl (phi l O (inc l O y))).1 ?_
    intro d hd
    rw [← hcomm, (fixed_relation_holds l O hl (inc l O y)).2 ⟨y, rfl⟩ d hd]
  · intro y' hy'
    obtain ⟨-, hinc, -, hphi⟩ := pi0Subst_reduction_holds l O k red hred
    obtain ⟨-, -, -, -, -, -, -, hinj⟩ := pi0Subst_laws_hold l k
    apply hinj hl
    rw [← hinc, ← hy', hphi, hinc, r5_character_holds l k]
    rfl
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
