-- Prove2me | solution 1 for D1Bound5.halfBinomialCoeff_convolution_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:17:09.809587+00:00
-- url     : https://prove2.me/submissions/ee220e0c-1db5-4d97-9f95-34959f938f85

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions

section
open Finset

namespace D1Bound5















/-- The half-binomial convolution vanishes at each degree at least two. -/
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) :
    (∑ ij ∈ Finset.antidiagonal n,
        halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2) = 0 := by
  have h := Ring.add_choose_eq
    (r := (1 / 2 : ℝ)) (s := (1 / 2 : ℝ)) n (Commute.all _ _)
  have hs : (1 / 2 : ℝ) + 1 / 2 = 1 := by ring
  rw [hs] at h
  have hz : Nat.choose 1 n = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hb0 : Ring.choose (1 : ℝ) n = 0 := by
    simpa [hz] using (Ring.choose_natCast (R := ℝ) 1 n)
  simpa [halfBinomialCoeff, hb0] using h.symm

end D1Bound5
end
