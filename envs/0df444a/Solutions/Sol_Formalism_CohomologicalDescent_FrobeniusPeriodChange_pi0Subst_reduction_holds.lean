-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.pi0Subst_reduction_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:14:59.749496+00:00
-- url     : https://prove2.me/submissions/16cffade-c15d-4da1-9d1a-199a53922f5c

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_map_reduction_binomialSeriesSubOne
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_map_reduction_pi0
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_binomialSeriesSubOne
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_one_add_X_pow_sub_one_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_pi0_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_subst_powerSeries


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
theorem _root_.solution : IncRed := by
  intro l _ O k _ _ _ _ red hred
  refine ⟨map_reduction_pi0 l O k red hred, ?_, ?_, ?_⟩
  · intro g
    unfold inc
    rw [map_subst_powerSeries red (hasSubst_pi0_alt l O), map_reduction_pi0 l O k red hred]
  · intro c f
    unfold act
    rw [map_subst_powerSeries red (hasSubst_binomialSeriesSubOne l O c), map_reduction_binomialSeriesSubOne l O k red hred]
  · intro f
    unfold phi
    rw [map_subst_powerSeries red (hasSubst_one_add_X_pow_sub_one_alt l)]
    simp
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
