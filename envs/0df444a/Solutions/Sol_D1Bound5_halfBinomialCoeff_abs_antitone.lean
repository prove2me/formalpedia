-- Prove2me | solution 1 for D1Bound5.halfBinomialCoeff_abs_antitone
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:16.858992+00:00
-- url     : https://prove2.me/submissions/35351318-ae27-455d-8fe8-fa53f5f2e040

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_halfBinomialCoeff_abs_next_le

section
open Finset

namespace D1Bound5









/-- Monotonicity of the absolute coefficients at all positive degrees. -/
theorem _root_.solution
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    |halfBinomialCoeff k| ≤ |halfBinomialCoeff j| := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_refl _
  | succ k hk ih =>
      exact (halfBinomialCoeff_abs_next_le k (hj.trans hk)).trans ih







end D1Bound5
end
