-- Prove2me | solution 1 for D1Bound5.halfBinomialCoeff_abs_le_half
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:44:37.983721+00:00
-- url     : https://prove2.me/submissions/f98233bf-2e0a-4008-a983-4023df891378

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_halfBinomialCoeff_abs_antitone

section
open Finset

namespace D1Bound5











/-- Uniform upper bound on each nonconstant half-binomial coefficient. -/
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    |halfBinomialCoeff n| ≤ (1 / 2 : ℝ) := by
  have h := halfBinomialCoeff_abs_antitone (j := 1) (k := n) (by decide) hn
  simpa [halfBinomialCoeff, Ring.choose_one_right] using h





end D1Bound5
end
