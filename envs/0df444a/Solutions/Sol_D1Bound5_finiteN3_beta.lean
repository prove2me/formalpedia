-- Prove2me | solution 1 for D1Bound5.finiteN3_beta
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:58.783678+00:00
-- url     : https://prove2.me/submissions/b7676096-75d8-499e-ae5d-becbaa44545d

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
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
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
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
import Theorems.Thm_D1Bound5_bennett_factorial_mul_abs_choose
import Theorems.Thm_D1Bound5_bennett_two_residual_choose_abs_Gamma

section
open Polynomial

namespace D1Bound5



theorem _root_.solution :
    Real.Gamma (9/2 : ℝ)*Real.Gamma (11/2 : ℝ)/
      (Real.pi*Real.Gamma (10 : ℝ)) = 35/65536 := by
  have h := bennett_factorial_mul_abs_choose (7/2 : ℝ) 9
  norm_num [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ] at h
  have hg := bennett_two_residual_choose_abs_Gamma 3 (by decide)
  norm_num only [Nat.cast_ofNat] at hg
  rw [← hg]
  nlinarith only [h]











end D1Bound5
end
