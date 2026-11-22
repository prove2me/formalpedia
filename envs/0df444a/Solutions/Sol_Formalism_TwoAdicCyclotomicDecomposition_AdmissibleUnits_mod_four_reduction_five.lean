-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.mod_four_reduction_five
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:15:47.899383+00:00
-- url     : https://prove2.me/submissions/40c77b7e-ee08-4b8d-a63c-9826badb44b6

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
theorem _root_.solution (N : ℕ) (h : 4 ∣ 2 ^ N) : r4 N h (u5 N) = 1 := by
  unfold u5
  show (ZMod.castHom h (ZMod 4)) ((5 : ℕ) : ZMod (2 ^ N)) = 1
  rw [map_natCast]
  decide
end Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
