-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.resMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:03:33.912892+00:00
-- url     : https://prove2.me/submissions/e1f2b6dd-a996-4c69-a4d8-dc19bfb87b23

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
theorem _root_.solution {s m : ℕ} (h : s ≤ m) (u : (ZMod (2 ^ (m + 2)))ˣ) (a b : ℤˣ) :
    resMap h (u, a, b) = (ZMod.unitsMap (pow_dvd_pow 2 (by omega)) u, a, b) := rfl
end Formalism.TwoAdicCyclotomicDecomposition
