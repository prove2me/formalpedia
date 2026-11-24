-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.coe_comp_pi0SubstHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:04:51.841103+00:00
-- url     : https://prove2.me/submissions/13be41ad-42fe-4a7e-ad7c-fde7871b8c96

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_pi0SubstHom_apply

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
theorem _root_.solution (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] {L : Type}
    [CommRing L] (jj : O⟦X⟧ →+* L⟦X⟧) :
    (⇑(jj.comp (pi0SubstHom l O))) = fun y => jj (inc l O y) := by
  funext y
  rw [RingHom.comp_apply, pi0SubstHom_apply]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
