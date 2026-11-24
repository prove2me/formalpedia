-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.mod_eight_reduction_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:37:19.914443+00:00
-- url     : https://prove2.me/submissions/fe058336-dc52-4b28-862d-b5b29a0c6c99

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
namespace Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
theorem _root_.solution (N : ℕ) (h : 8 ∣ 2 ^ N) : r8 N h (u3 N) = 3 := by
  unfold u3
  show (ZMod.castHom h (ZMod 8)) ((3 : ℕ) : ZMod (2 ^ N)) = 3
  rw [map_natCast]
  decide
end Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
