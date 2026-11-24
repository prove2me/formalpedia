-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.fact_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:37:47.110554+00:00
-- url     : https://prove2.me/submissions/df265897-f599-434a-a265-487d626d48d3

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset MeasureTheory
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution (a b N i : ℕ) (hab : a ≤ b) (hi : i ≤ N) :
    (a + N - i).factorial ≤ a.factorial * (b + N + 1) ^ (N + 1) := by
  have e := Nat.factorial_mul_descFactorial (n := a + N - i) (k := N - i) (by omega)
  have e2 : a + N - i - (N - i) = a := by omega
  rw [e2] at e
  rw [← e]
  apply Nat.mul_le_mul_left
  calc (a + N - i).descFactorial (N - i) ≤ (a + N - i) ^ (N - i) := Nat.descFactorial_le_pow _ _
    _ ≤ (b + N + 1) ^ (N - i) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (b + N + 1) ^ (N + 1) := Nat.pow_le_pow_right (by omega) (by omega)
end Formalism.LogVandermondeBounds.flipTwoThree
