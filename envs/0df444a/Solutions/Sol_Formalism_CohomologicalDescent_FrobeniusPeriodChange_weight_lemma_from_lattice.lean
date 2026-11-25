-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.weight_lemma_from_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:20:30.708822+00:00
-- url     : https://prove2.me/submissions/3ba5bce0-bf9c-41a2-ab08-ea36faf5db4c

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_alpha_bounds_hold
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_weight_lemma_full
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_weight_inputs_of_norm

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
theorem _root_.solution : LemmaWFromLattice := by
  intro ι _ σ l h t n _ O F L _ _ _ _ _ _ I _ W u c U' wt kap ζ em jj hl2 hN
  have hW := weight_inputs_of_norm ι σ l h t n O F L I W u c U' wt kap ζ em jj hl2 hN
  obtain ⟨h1, h2, h3⟩ := weight_lemma_full ι σ l h t n O F W u c U' wt kap hl2 hW
  exact ⟨alpha_bounds_hold ι σ l h t n O F W u c U' wt kap hl2 hW, h1, h2, h3⟩
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
