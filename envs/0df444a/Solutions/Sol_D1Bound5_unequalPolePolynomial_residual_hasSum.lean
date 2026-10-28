-- Prove2me | solution 1 for D1Bound5.unequalPolePolynomial_residual_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:23:24.480777+00:00
-- url     : https://prove2.me/submissions/03af54c2-89be-48d8-a134-d8b8eee8a5dd

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_UnequalPoleResidual_Definitions
import Theorems.Thm_D1Bound5_bennett_polynomial_series_hasSum
import Theorems.Thm_D1Bound5_bennett_rescaled_binomial_hasSum

section
open Finset

namespace D1Bound5

variable {I : Type*} [Fintype I] [DecidableEq I]



theorem _root_.solution
    (a : I → ℂ) (e : I → ℕ) (k : ℕ) (ν x : ℂ)
    (hx : ∀ j, ‖a j*x‖ < 1) :
    HasSum (fun r : ℕ => PowerSeries.coeff r
      (∑ j, (unequalPolePolynomial a e k ν j : PowerSeries ℂ)*
        PowerSeries.rescale (a j) (PowerSeries.binomialSeries ℂ ν))*x^r)
      (∑ j, (unequalPolePolynomial a e k ν j).eval x*(1+a j*x)^ν) := by
  have hh (j : I) :=
    bennett_rescaled_binomial_hasSum (a j) ν x (hx j)
  have hp (j : I) := bennett_polynomial_series_hasSum
    (unequalPolePolynomial a e k ν j)
    (PowerSeries.rescale (a j) (PowerSeries.binomialSeries ℂ ν))
    x ((1+a j*x)^ν) (hh j).1 (hh j).2
  simpa only [map_sum,Finset.sum_mul] using
    hasSum_sum (s := (univ : Finset I)) (fun j _ => hp j)









end D1Bound5
end
