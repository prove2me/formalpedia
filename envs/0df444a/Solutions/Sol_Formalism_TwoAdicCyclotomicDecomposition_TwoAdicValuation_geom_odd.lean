-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.geom_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:37:26.467512+00:00
-- url     : https://prove2.me/submissions/781187d5-32c0-4964-8440-3b749055473e

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
theorem _root_.solution (a : ℤ) (ha : Odd a) (n : ℕ) : (Odd (∑ i ∈ Finset.range n, a ^ i) ↔ Odd n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : ¬ Even (a ^ n) := Int.not_even_iff_odd.mpr (ha.pow)
    rw [Finset.sum_range_succ, Int.odd_add, ih]
    simp [hp, Nat.odd_add_one]
end Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
