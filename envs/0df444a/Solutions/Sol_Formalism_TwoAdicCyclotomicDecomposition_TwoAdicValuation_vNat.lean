-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.vNat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:37:29.00213+00:00
-- url     : https://prove2.me/submissions/91ba62ac-8efa-4802-b944-caaf541ffb6d

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
theorem _root_.solution (e : ℕ) (he : e ≠ 0) : (padicValNat 2 e : ℕ∞) = emultiplicity (2 : ℤ) (e : ℤ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat_eq_emultiplicity he, ← Int.natCast_emultiplicity]
  rfl
end Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
