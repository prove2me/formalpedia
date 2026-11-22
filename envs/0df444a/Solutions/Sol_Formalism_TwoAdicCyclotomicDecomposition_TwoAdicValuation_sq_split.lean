-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.sq_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:16:49.037354+00:00
-- url     : https://prove2.me/submissions/0a3cbffb-1056-414a-b759-fe9e1178d3d5

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
namespace Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
theorem _root_.solution (a : ℤ) (ha2 : a ^ 2 ≠ 1) :
    padicValInt 2 (a ^ 2 - 1) = padicValInt 2 (a - 1) + padicValInt 2 (a + 1) := by
  have h1 : a - 1 ≠ 0 := by
    intro h; apply ha2; rw [sub_eq_zero.mp h]; norm_num
  have h2 : a + 1 ≠ 0 := by
    intro h; apply ha2; rw [show a = -1 by linarith]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show a ^ 2 - 1 = (a - 1) * (a + 1) by ring, padicValInt.mul h1 h2]
end Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
