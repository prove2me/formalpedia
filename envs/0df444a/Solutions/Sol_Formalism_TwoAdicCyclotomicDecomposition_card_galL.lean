-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.card_galL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:20.614125+00:00
-- url     : https://prove2.me/submissions/257d22e9-9e1b-42cf-adf1-9e1a93e42be5

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Polynomial
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {n q d : ℕ} {ζ a b : L}
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (hn : 1 ≤ n) : Nat.card (GalL n) = 2 ^ (n + 1) := by
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (by omega), Nat.card_eq_fintype_card,
    Fintype.card_units_int]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring
end Formalism.TwoAdicCyclotomicDecomposition
