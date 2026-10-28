-- Prove2me | solution 1 for D1Bound5.halfBinomialCoeff_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:03.124543+00:00
-- url     : https://prove2.me/submissions/a56ed921-c54f-49c4-b44b-73f2eb6a6cce

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



/-- The half-binomial coefficient recurrence in every degree. -/
theorem _root_.solution (n : ℕ) :
    (n + 1 : ℝ) * halfBinomialCoeff (n + 1) =
      ((1 / 2 : ℝ) - n) * halfBinomialCoeff n := by
  have h := Ring.choose_smul_choose (r := (1 / 2 : ℝ))
    (n := n + 1) (k := n) (Nat.le_succ n)
  simpa [halfBinomialCoeff, Nat.choose_succ_self_right, nsmul_eq_mul,
    Ring.choose_one_right, mul_comm, mul_left_comm, mul_assoc] using h













end D1Bound5
end
