-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.prime_sub_one_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:21.780558+00:00
-- url     : https://prove2.me/submissions/cffa58e2-df4a-46b6-a858-8fbf1aa258e7

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
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : 0 < l - 1 := by
  have := (Fact.out : l.Prime).two_le
  omega
end Formalism.CohomologicalDescent.HeightDescentMinors
