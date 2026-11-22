-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.exists_algHom_act
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:34.333812+00:00
-- url     : https://prove2.me/submissions/2b6800cf-a508-4dd9-9724-69ed502ff2ff

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_br_padic

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
theorem _root_.solution (c : ℤ_[l]) :
    ∃ Φ : O⟦X⟧ →ₐ[O] O⟦X⟧, ∀ f, act l O c f = Φ f := by
  refine ⟨PowerSeries.substAlgHom (hasSubst_br_padic l O c), fun f => ?_⟩
  rw [act, PowerSeries.coe_substAlgHom]
end Formalism.CohomologicalDescent.HeightDescentMinors
