-- Prove2me | solution 1 for D1Bound5.ordinary_height_power_upper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:05:47.574391+00:00
-- url     : https://prove2.me/submissions/62370441-b460-4ee0-8a8f-06956d9ce3ca

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
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Definitions.Def_D1Bound5_TwoSmallHeightScalar_Definitions
import Theorems.Thm_D1Bound5_ordinaryLog10_mono
import Theorems.Thm_D1Bound5_ordinaryLog10_mul
import Theorems.Thm_D1Bound5_ordinaryLog10_pow
import Theorems.Thm_D1Bound5_ordinaryLog10_ten

section
open scoped NumberField
open Module

namespace D1Bound5

theorem _root_.solution (P Q : ℝ) (hP : (10 : ℝ)^40 ≤ P) (hQ : 0 < Q)
    (hh : ordinaryLog10 Q < twoSmallHeightEnvelope (ordinaryLog10 P)) :
    Q < (10 : ℝ)^60*P^7 := by
  have hP0 : 0 < P := by norm_num at hP; linarith only [hP]
  have hx : 40 ≤ ordinaryLog10 P := by
    have hh := ordinaryLog10_mono (by positivity : (0 : ℝ) < 10^40) hP
    simpa only [ordinaryLog10_pow,ordinaryLog10_ten,Nat.cast_ofNat,mul_one] using hh
  have hr : (4047/25 : ℝ)/(ordinaryLog10 P-4) ≤ (4047/25)/36 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hx])
  have hg : twoSmallHeightEnvelope (ordinaryLog10 P) < 7*ordinaryLog10 P+60 := by
    dsimp [twoSmallHeightEnvelope]
    norm_num at hr
    linarith only [hr]
  have hlog : ordinaryLog10 Q < ordinaryLog10 ((10 : ℝ)^60*P^7) := by
    rw [ordinaryLog10_mul _ _ (by positivity) (by positivity),ordinaryLog10_pow,
      ordinaryLog10_pow,ordinaryLog10_ten]
    norm_num
    linarith only [hh,hg]
  by_contra hbad
  have hrev := ordinaryLog10_mono (by positivity : 0 < (10 : ℝ)^60*P^7) (le_of_not_gt hbad)
  linarith only [hlog,hrev]









end D1Bound5
end
