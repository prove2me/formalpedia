-- Prove2me | solution 1 for D1Bound5.halfBinomialCoeff_abs_convolution
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:37:54.115534+00:00
-- url     : https://prove2.me/submissions/c7a5b71c-1e3c-41f8-b0cb-9b0a37f3046d

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_halfBinomialCoeff_interior_abs_sum

section
open Finset

namespace D1Bound5









/-- Sharp absolute half-binomial convolution, valid at every degree >= 2. -/
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) :
    (∑ ij ∈ Finset.antidiagonal n,
      |halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2|) =
        4 * |halfBinomialCoeff n| := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 = (k + 1) + 1 by omega,
    Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.sum_antidiagonal_succ']
  have hb0 : halfBinomialCoeff 0 = 1 := by
    simp [halfBinomialCoeff]
  simp only [hb0, one_mul, mul_one]
  rw [halfBinomialCoeff_interior_abs_sum]
  ring

end D1Bound5
end
