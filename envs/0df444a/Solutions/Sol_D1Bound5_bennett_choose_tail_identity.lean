-- Prove2me | solution 1 for D1Bound5.bennett_choose_tail_identity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:59:12.831391+00:00
-- url     : https://prove2.me/submissions/a7363273-a278-42b9-80cd-0f0dae697762

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
/-!
An elementary analytic majorant for the actual binomial/homogeneous tail that
arises in Bennett's simultaneous approximants.  In contrast to a coefficient
envelope interface, every coefficient of the series below is specified.

The algebraic identification of the residue moments with homogeneous
polynomials is a separate theorem.  This file does not assume that an arbitrary
series is a Bennett residual.  Once that identification is available, the
specialization n = 3k, s = k + 1/2 gives exactly the eta exponent in the paper.
-/

namespace D1Bound5





/-- Exact coefficient identity responsible for cancellation of the homogeneous
coefficient counting factor. -/
theorem _root_.solution (s : ℝ) (n t : ℕ) :
    |Ring.choose s (n + t)| * (Nat.choose (n + t) t : ℝ) =
      |Ring.choose s n| * |Ring.choose (s - n) t| := by
  have h := Ring.choose_smul_choose s (n := n + t) (k := n)
    (Nat.le_add_right n t)
  rw [Nat.add_sub_cancel_left, nsmul_eq_mul] at h
  have ha := congrArg abs h
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)] at ha
  rw [Nat.choose_symm_add] at ha
  simpa only [mul_comm] using ha







end D1Bound5
end
