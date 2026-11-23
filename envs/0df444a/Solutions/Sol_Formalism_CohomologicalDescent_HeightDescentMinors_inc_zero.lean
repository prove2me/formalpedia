-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.inc_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:33.432809+00:00
-- url     : https://prove2.me/submissions/db81b22e-95d5-4737-85cc-2ca2368a384f

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
theorem _root_.solution : inc l O 0 = 0 := by
  rw [inc, ← PowerSeries.coe_substAlgHom (hasSubst_pi0_alt l O), map_zero]
end Formalism.CohomologicalDescent.HeightDescentMinors
