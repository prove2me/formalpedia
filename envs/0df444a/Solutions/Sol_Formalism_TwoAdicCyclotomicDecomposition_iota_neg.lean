-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.iota_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:03:31.847592+00:00
-- url     : https://prove2.me/submissions/a7b2c8d3-654c-47e1-8aba-a8dd7d351994

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (n : ℕ) : iota n (-1) = -1 := by
  ext
  simp [iota]
end Formalism.TwoAdicCyclotomicDecomposition
