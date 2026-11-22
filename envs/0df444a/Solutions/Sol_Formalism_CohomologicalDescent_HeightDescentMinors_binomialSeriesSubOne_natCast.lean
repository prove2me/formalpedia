-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.binomialSeriesSubOne_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:07.811081+00:00
-- url     : https://prove2.me/submissions/0ac990a4-4d35-4632-8e62-f81e1ed9db9e

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

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
theorem _root_.solution (n : ℕ) : br l O (n : ℤ_[l]) = (1 + X) ^ n - 1 := by
  rw [br, PowerSeries.binomialSeries_nat]
end Formalism.CohomologicalDescent.HeightDescentMinors
