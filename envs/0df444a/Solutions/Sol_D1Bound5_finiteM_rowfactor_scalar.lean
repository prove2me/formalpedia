-- Prove2me | solution 1 for D1Bound5.finiteM_rowfactor_scalar
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:57:25.55102+00:00
-- url     : https://prove2.me/submissions/b32a262a-86f3-47ab-931c-367fc6423331

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- Uniform row-factor geometry. Only the elementary upper bounds for the
three differences enter; no lower separation estimate is assumed. -/
theorem _root_.solution (A B S x y z r : ℝ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hBS : B ≤ S)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxB : x ≤ 2*B) (hyS : y ≤ 2*S) (hzS : z ≤ 2*S)
    (hr : r=x*y*z ∨ r=A*z ∨ r=B*y ∨ r=S*x) :
    A*(x*y*z)^4 ≤ 2048*B^4*S^7*r := by
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hS1 : 1 ≤ S := hA.trans (hAB.trans hBS)
  rcases hr with rfl | rfl | rfl | rfl
  · have hcomp : A*x^3*y^3*z^3 ≤ B*(2*B)^3*(2*S)^3*(2*S)^3 := by gcongr
    have hsp : S^6 ≤ S^7 := pow_le_pow_right₀ hS1 (by decide)
    have hwide : A*x^3*y^3*z^3 ≤ 2048*B^4*S^7 := by
      have hpow := mul_le_mul_of_nonneg_left hsp (show 0 ≤ 512*B^4 by positivity)
      have hpos : 0 ≤ B^4*S^7 := by positivity
      nlinarith only [hcomp,hpow,hpos]
    have hm := mul_le_mul_of_nonneg_right hwide (show 0 ≤ x*y*z by positivity)
    nlinarith only [hm]
  · have hcomp : x^4*y^4*z^3 ≤ (2*B)^4*(2*S)^4*(2*S)^3 := by gcongr
    have hm := mul_le_mul_of_nonneg_right hcomp (show 0 ≤ A*z by positivity)
    nlinarith only [hm]
  · have hcomp : A*x^4*y^3*z^4 ≤ B*(2*B)^4*(2*S)^3*(2*S)^4 := by gcongr
    have hm := mul_le_mul_of_nonneg_right hcomp hy.le
    nlinarith only [hm]
  · have hcomp : A*x^3*y^4*z^4 ≤ B*(2*B)^3*(2*S)^4*(2*S)^4 := by gcongr
    have hm := mul_le_mul_of_nonneg_right hcomp hx.le
    nlinarith only [hm]



end D1Bound5
end
