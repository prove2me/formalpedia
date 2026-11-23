-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.exists_algHom_inc_pi0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:32.698687+00:00
-- url     : https://prove2.me/submissions/89374d76-3931-44bd-b733-ce2fb00b2a25

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_pi0_alt

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
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (hm : MuFacts) :
    ∃ Φ : O⟦X⟧ →ₐ[O] O⟦X⟧, (∀ f, inc l O f = Φ f) ∧ Φ X = pi0 l O := by
  refine ⟨PowerSeries.substAlgHom (hasSubst_pi0_alt l O), fun f => ?_, ?_⟩
  · rw [inc, PowerSeries.coe_substAlgHom]
  · rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_X (hasSubst_pi0_alt l O)]
end Formalism.CohomologicalDescent.HeightDescentMinors
