-- Prove2me | solution 1 for DiazModulus.strong_six_exponentials_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T09:53:54.019929+00:00
-- url     : https://prove2.me/submissions/d5d6dd10-039b-40c0-a9f5-bfaba121c95c

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_strong_six_exponentials
import Theorems.Thm_DiazModulus_multiplicityEstimateElem

open Complex ComplexConjugate

/-! # Roy's strong six exponentials theorem, unconditional

The node `strong_six_exponentials` proves Roy's strong six exponentials theorem under the hypothesis
`MultiplicityEstimateElem`, and the node `multiplicityEstimateElem` proves that proposition. Applying the first
to the second gives the theorem with no hypothesis: for `x ∈ ℂ²` and `y ∈ ℂ³`, each linearly independent over the
algebraic numbers, some product `x_i y_j` lies outside the `Q̄`-span `ℒ̃` of `1` and the logarithms of algebraic
numbers. -/

open DiazModulus in
theorem solution :
    ∀ x : Fin 2 → ℂ, ∀ y : Fin 3 → ℂ, LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ ∀ i j, x i * y j ∈ LogAlgTilde := by
  exact DiazModulus.strong_six_exponentials DiazModulus.multiplicityEstimateElem
