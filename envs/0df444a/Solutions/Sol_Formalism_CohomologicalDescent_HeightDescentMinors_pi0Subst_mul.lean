-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.pi0Subst_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:34.167447+00:00
-- url     : https://prove2.me/submissions/280cbeff-31aa-43d7-b66f-0d4cf6c67ade

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
theorem _root_.solution (f g : O⟦X⟧) : inc l O (f * g) = inc l O f * inc l O g := by
  rw [inc, inc, inc, ← PowerSeries.coe_substAlgHom (hasSubst_pi0_alt l O), map_mul]
end Formalism.CohomologicalDescent.HeightDescentMinors
