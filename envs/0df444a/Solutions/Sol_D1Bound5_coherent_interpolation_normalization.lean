-- Prove2me | solution 1 for D1Bound5.coherent_interpolation_normalization
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:54.573459+00:00
-- url     : https://prove2.me/submissions/7a4d1560-7caa-4d37-aca1-bc81d1105d22

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Finset Polynomial

namespace D1Bound5













end D1Bound5




open Finset

namespace D1Bound5

/-- Algebraic normalization of the paper's coherent form.  Here `g i`
denotes the product of the two analytic square-root factors and `q`
denotes the remaining square-root factor.  The result applies to any
nonzero choice of Vandermonde factor `Delta` and square-root scale `eta`.
No denominator at an individual anchor is cancelled in this proof. -/
theorem _root_.solution
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a g : ι → ℂ) (q Delta eta : ℂ)
    (hm : 2 ≤ s.card) (hDelta : Delta ≠ 0) (heta : eta ≠ 0) :
    (-Delta * (eta * q) +
      ∑ i ∈ s, (Delta * (a i) ^ (s.card - 2) /
        (∏ j ∈ s.erase i, (a i - a j))) * (a i * eta * g i)) /
      (Delta * eta) =
      (∑ i ∈ s, ((a i) ^ (s.card - 1) /
        (∏ j ∈ s.erase i, (a i - a j))) * g i) - q := by
  have hexp : s.card - 1 = (s.card - 2) + 1 := by omega
  have hsum :
      (∑ i ∈ s, (Delta * (a i) ^ (s.card - 2) /
        (∏ j ∈ s.erase i, (a i - a j))) * (a i * eta * g i)) =
      Delta * eta * ∑ i ∈ s, ((a i) ^ (s.card - 1) /
        (∏ j ∈ s.erase i, (a i - a j))) * g i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hexp, pow_succ]
    ring
  rw [hsum]
  apply (div_eq_iff (mul_ne_zero hDelta heta)).2
  ring

end D1Bound5




open Finset

namespace D1Bound5





end D1Bound5




namespace D1Bound5









end D1Bound5
end
