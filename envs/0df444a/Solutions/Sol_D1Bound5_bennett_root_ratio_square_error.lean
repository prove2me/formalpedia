-- Prove2me | solution 1 for D1Bound5.bennett_root_ratio_square_error
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:54:55.52476+00:00
-- url     : https://prove2.me/submissions/9bbfbb99-c247-40f7-8ce8-2bc9e580f874

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5



/-- Exact algebraic error for the two products of tuple roots. -/
theorem _root_.solution
    (a c d z r v θ : ℂ) (ha : a ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0)
    (hr : r ^ 2 = a * c + 1) (hv : v ^ 2 = a * d + 1)
    (hzsq : z ^ 2 = c * d + 1) (hθ : θ ^ 2 = 1 + 1 / (a * c)) :
    (r * v / (a * z)) ^ 2 - θ ^ 2 =
      θ ^ 2 * (c - a) / (a * z ^ 2) := by
  have hcd : c * d + 1 ≠ 0 := by rw [← hzsq]; exact pow_ne_zero _ hz
  simp only [div_pow, mul_pow, hr, hv, hθ, hzsq]
  field_simp [ha, hc, hcd]
  <;> ring







end D1Bound5
end
