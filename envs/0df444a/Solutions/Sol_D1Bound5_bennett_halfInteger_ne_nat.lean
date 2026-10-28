-- Prove2me | solution 1 for D1Bound5.bennett_halfInteger_ne_nat
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:21.00189+00:00
-- url     : https://prove2.me/submissions/238f3e58-bed2-44af-be45-03ed7820fb72

import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination

section
open Polynomial

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



/-- Every half-integer parameter in the Bennett node-removal induction
differs from every natural number. This is the exact parity obstruction,
transported through the characteristic-zero cast. -/
theorem _root_.solution (k v j : ℕ) :
    (k : F) + (1 / 2 : F) - (v : F) * (k : F) ≠ (j : F) := by
  intro h
  have heF : ((2 * k + 1 : ℕ) : F) = ((2 * (v * k + j) : ℕ) : F) := by
    push_cast
    linear_combination (2 : F) * h
  have heN : 2 * k + 1 = 2 * (v * k + j) := Nat.cast_injective heF
  omega



end D1Bound5
end
