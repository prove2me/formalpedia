-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.five_unit_coe_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:22:52.206436+00:00
-- url     : https://prove2.me/submissions/8aa665e6-f349-40b6-b5be-3234fe12b16c

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
theorem _root_.solution (n : ℕ) : ((u5 n : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n)) = ((5 : ℕ) : ZMod (2 ^ n)) := by simp [u5, ZMod.coe_unitOfCoprime]
end Formalism.TwoAdicCyclotomicDecomposition
