-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.inc_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:33.563545+00:00
-- url     : https://prove2.me/submissions/1860b05b-05f5-4b66-925c-ee81f6d5967b

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
theorem _root_.solution (f : O⟦X⟧) (n : ℕ) : inc l O (f ^ n) = inc l O f ^ n := by
  rw [inc, inc, ← PowerSeries.coe_substAlgHom (hasSubst_pi0_alt l O), map_pow]
end Formalism.CohomologicalDescent.HeightDescentMinors
