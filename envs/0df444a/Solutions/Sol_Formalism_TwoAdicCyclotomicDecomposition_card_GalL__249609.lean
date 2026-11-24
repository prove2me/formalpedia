-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.card_GalL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:03:29.237006+00:00
-- url     : https://prove2.me/submissions/5d3ef696-445e-4fe0-abbd-0e8649ca3dc0

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
theorem _root_.solution (n : ℕ) : Nat.card (GalL (n + 2)) = 2 ^ (n + 3) := by
  rw [Nat.card_prod, Nat.card_prod, card_units, card_int_units_eq_two]
  ring
end Formalism.TwoAdicCyclotomicDecomposition
