-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.vEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:37:28.052034+00:00
-- url     : https://prove2.me/submissions/8800ce80-07dd-4314-b6cc-e2dceda1ea37

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
theorem _root_.solution (z : ℤ) (hz : z ≠ 0) : (padicValInt 2 z : ℕ∞) = emultiplicity (2 : ℤ) z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show padicValInt 2 z = padicValNat 2 z.natAbs from rfl,
    padicValNat_eq_emultiplicity (Int.natAbs_ne_zero.mpr hz), Int.emultiplicity_natAbs]
  rfl
end Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
