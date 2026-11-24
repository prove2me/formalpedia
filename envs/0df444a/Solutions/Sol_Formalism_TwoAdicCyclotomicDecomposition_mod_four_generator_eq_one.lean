-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.mod_four_generator_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:05:17.379806+00:00
-- url     : https://prove2.me/submissions/95ec4e01-9ce9-45fd-9205-d932e92752a6

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
theorem _root_.solution (s m : ℕ) : r4 m (wgen s m) = 1 := by rw [wgen, map_pow, mod_four_reduction_five, one_pow]
end Formalism.TwoAdicCyclotomicDecomposition
