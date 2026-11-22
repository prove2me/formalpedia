-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.rankBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:33.813707+00:00
-- url     : https://prove2.me/submissions/1d3a5ac0-c6dc-4ba7-aa9f-ef9b43d5249a

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Groups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
open scoped commutatorElement
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : RankBound := by
  intro r hr
  constructor
  · intro h
    by_contra hlt
    have h1 : r * 4 ≤ r * (r - 1) := Nat.mul_le_mul_left r (by omega)
    generalize r * (r - 1) = t at h h1
    omega
  · intro h
    interval_cases r <;> decide
end Formalism.TwoAdicCyclotomicDecomposition
