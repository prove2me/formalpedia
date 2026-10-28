-- Prove2me | solution 1 for D1Bound5.two_small_large_S_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:42:22.688438+00:00
-- url     : https://prove2.me/submissions/6adf5218-cbb5-413f-bb3d-045fe24563f5

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

section
namespace D1Bound5

/-- Exact size checks for the separated V window when the third entry
is at least 10^8. The deliberately weaker C>ST/4 simplifies the scalar
closure without changing the final cutoff. -/
theorem _root_.solution
    (A B S T C D : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hB3 : B < 3)
    (hS : (10 : ℝ)^8 ≤ S) (hST : S ≤ T)
    (hC : (3/8 : ℝ)*A*S*T < C) (hD : 2*S*T*C < D)
    (hcross : A^3*B*T^3*C/(7*S) < D) :
    1000 ≤ C ∧ 4*T ≤ C ∧ 4*C ≤ D ∧
      32*B*S*T/A^3 ≤ C^2 ∧ 101*B^2*T^4/C < D := by
  have hS0 : 0 < S := by norm_num at hS; linarith only [hS]
  have hT0 : 0 < T := hS0.trans_le hST
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hB]
  have hA3 : 1 ≤ A^3 := by calc
    1 = (1 : ℝ)^3 := by norm_num
    _ ≤ A^3 := by gcongr
  have hprod : (10 : ℝ)^16 ≤ S*T := by
    have hh := mul_le_mul hS (hS.trans hST) (by positivity : (0 : ℝ) ≤ 10^8) hS0.le
    norm_num at hh ⊢
    exact hh
  have hC4 : S*T < 4*C := by
    have hh := mul_le_mul_of_nonneg_right hA (mul_nonneg hS0.le hT0.le)
    have hp := mul_pos hS0 hT0
    nlinarith only [hC,hh,hp]
  have hC0 : 0 < C := by nlinarith only [hC4,mul_pos hS0 hT0]
  have hCsq : S^2*T^2 < 16*C^2 := by
    have hh := mul_pos (sub_pos.mpr hC4) (by positivity : 0 < 4*C+S*T)
    nlinarith only [hh]
  have hSTC : 1000 ≤ C := by norm_num at hprod; nlinarith only [hprod,hC4]
  have hTC : 4*T ≤ C := by
    have hh := mul_le_mul_of_nonneg_right hS hT0.le
    norm_num at hh
    nlinarith only [hh,hC4,hT0]
  have hCD : 4*C ≤ D := by
    have hh := mul_le_mul_of_nonneg_right hprod hC0.le
    norm_num at hh
    nlinarith only [hh,hD,hC0]
  have hsize : 32*B*S*T/A^3 ≤ C^2 := by
    have hSTbig : 1536*S*T ≤ S^2*T^2 := by
      have hh := mul_le_mul_of_nonneg_right hprod (mul_nonneg hS0.le hT0.le)
      norm_num at hh
      nlinarith only [hh,mul_nonneg hS0.le hT0.le]
    have hBprod := mul_lt_mul_of_pos_right hB3 (mul_pos hS0 hT0)
    have hAC := mul_le_mul_of_nonneg_right hA3 (sq_nonneg C)
    apply (div_le_iff₀ (by positivity : 0 < A^3)).2
    nlinarith only [hCsq,hSTbig,hBprod,hAC]
  have hwindow : 101*B^2*T^4/C < D := by
    have hSTbig : 33936*S*T < S^2*T^2 := by
      have hh := mul_le_mul_of_nonneg_right hprod (mul_nonneg hS0.le hT0.le)
      norm_num at hh
      nlinarith only [hh,mul_pos hS0 hT0]
    have hBprod := mul_lt_mul_of_pos_right hB3 (mul_pos hS0 hT0)
    have hAC := mul_le_mul_of_nonneg_right hA3 (sq_nonneg C)
    have hcore : 707*B*S*T < A^3*C^2 := by
      nlinarith only [hSTbig,hBprod,hAC,hCsq]
    have hm := mul_lt_mul_of_pos_right hcore (by positivity : 0 < B*T^3)
    have hcompare : 101*B^2*T^4/C < A^3*B*T^3*C/(7*S) := by
      apply (div_lt_div_iff₀ hC0 (by positivity : 0 < 7*S)).2
      nlinarith only [hm]
    exact hcompare.trans hcross
  exact ⟨hSTC,hTC,hCD,hsize,hwindow⟩



end D1Bound5
end
