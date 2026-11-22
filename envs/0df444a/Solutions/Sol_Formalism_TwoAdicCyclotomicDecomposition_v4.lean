-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.v4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:42.654588+00:00
-- url     : https://prove2.me/submissions/184b152f-e497-4da6-a1ac-8c6b7f044d6f

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral

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
theorem _root_.solution : padicValInt 2 ((5 : ℤ) - 1) = 2 := by
  have : ((5 : ℤ) - 1) = ((2 ^ 2 : ℕ) : ℤ) := by norm_num
  rw [this, padicValInt.of_nat, padicValNat.prime_pow]
end Formalism.TwoAdicCyclotomicDecomposition
