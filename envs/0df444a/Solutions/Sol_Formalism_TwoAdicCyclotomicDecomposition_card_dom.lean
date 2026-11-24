-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.card_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:03:31.408953+00:00
-- url     : https://prove2.me/submissions/6bbb2ef7-07d5-4215-9a09-f388d88152c7

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
section
namespace Formalism.TwoAdicCyclotomicDecomposition
private lemma card_int_units_eq_two : Nat.card ℤˣ = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
end Formalism.TwoAdicCyclotomicDecomposition
end

set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (s m : ℕ) :
    Nat.card (ℤˣ × Multiplicative (ZMod (2 ^ (m - s)))) = 2 ^ (m - s + 1) := by
  rw [Nat.card_prod, card_int_units_eq_two, card_mz]
  ring
end Formalism.TwoAdicCyclotomicDecomposition
