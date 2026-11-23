-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.phi_eq_act_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:02.036663+00:00
-- url     : https://prove2.me/submissions/b5798f1e-ad60-4765-a00b-3aa2f5cd30e8

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialSeriesSubOne_natCast

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
theorem _root_.solution (f : O⟦X⟧) : phi l O f = act l O (l : ℤ_[l]) f := by
  rw [phi, act, binomialSeriesSubOne_natCast]
end Formalism.CohomologicalDescent.HeightDescentMinors
