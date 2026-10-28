-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.one_small_first_pair_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:09:10.666246+00:00
-- url     : https://prove2.me/submissions/cbd51982-19e1-4719-9510-9689ec49ebc1

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.Convert
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
import Definitions.Def_D1Bound5_FiveRegionParameters_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_IsD1Tuple_five_region_impossible
import Theorems.Thm_D1Bound5_norm_sq_eq_absolute_norm
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The five unbounded regions give the manuscript first-pair reduction
in the actual full integer ring. Integrality of the squared complex
modulus is obtained from the proved algebraic norm identity. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hA : ‖phi (a 0 : K)‖ < 3) (hB : 3 ≤ ‖phi (a 1 : K)‖) :
    (Algebra.norm ℤ (a 0)=1 ∧ ‖phi (a 1 : K)‖ < 8) ∨
      (Algebra.norm ℤ (a 0)=2 ∧ ‖phi (a 1 : K)‖ < 4) := by
  let N : ℤ := Algebra.norm ℤ (a 0)
  have hnorm : ‖phi (a 0 : K)‖^2=(N : ℝ) := norm_sq_eq_absolute_norm hK phi (a 0)
  have hA1 := one_le_norm_integer hK phi (ha.2.1 0)
  have hN1 : 1 ≤ N := by
    have hh : (1 : ℝ) ≤ (N : ℝ) := by rw [← hnorm]; nlinarith only [hA1]
    exact_mod_cast hh
  have hN9 : N < 9 := by
    have hh : (N : ℝ) < 9 := by
      rw [← hnorm]
      nlinarith only [hA,hA1]
    exact_mod_cast hh
  have hN8 : ‖phi (a 0 : K)‖^2 ≤ 8 := by
    rw [hnorm]
    exact_mod_cast (show N ≤ 8 by omega)
  by_cases hNunit : N=1
  · by_cases hB8 : ‖phi (a 1 : K)‖ < 8
    · exact Or.inl ⟨hNunit,hB8⟩
    · exfalso
      apply ha.five_region_impossible hK phi a hmon 0 hN8
      rw [FiveRegionCase,if_neg (by decide : (0 : Fin 5) ≠ 4)]
      change ‖phi (a 0 : K)‖^2 = 1 ∧ 8 ≤ ‖phi (a 1 : K)‖
      exact ⟨by rw [hnorm,hNunit]; norm_num,le_of_not_gt hB8⟩
  by_cases hNtwo : N=2
  · by_cases hB4 : ‖phi (a 1 : K)‖ < 4
    · exact Or.inr ⟨hNtwo,hB4⟩
    · exfalso
      apply ha.five_region_impossible hK phi a hmon 1 hN8
      rw [FiveRegionCase,if_neg (by decide : (1 : Fin 5) ≠ 4)]
      change ‖phi (a 0 : K)‖^2 = 2 ∧ 4 ≤ ‖phi (a 1 : K)‖
      exact ⟨by rw [hnorm,hNtwo]; norm_num,le_of_not_gt hB4⟩
  by_cases hNthree : N=3
  · exfalso
    apply ha.five_region_impossible hK phi a hmon 2 hN8
    rw [FiveRegionCase,if_neg (by decide : (2 : Fin 5) ≠ 4)]
    change ‖phi (a 0 : K)‖^2 = 3 ∧ 3 ≤ ‖phi (a 1 : K)‖
    exact ⟨by rw [hnorm,hNthree]; norm_num,hB⟩
  by_cases hNfour : N=4
  · exfalso
    apply ha.five_region_impossible hK phi a hmon 3 hN8
    rw [FiveRegionCase,if_neg (by decide : (3 : Fin 5) ≠ 4)]
    change ‖phi (a 0 : K)‖^2 = 4 ∧ 3 ≤ ‖phi (a 1 : K)‖
    exact ⟨by rw [hnorm,hNfour]; norm_num,hB⟩
  exfalso
  apply ha.five_region_impossible hK phi a hmon 4 hN8
  norm_num [FiveRegionCase,fiveRegionMinNorm,fiveRegionMinB]
  refine ⟨?_,hB⟩
  rw [hnorm]
  exact_mod_cast (show 5 ≤ N by omega)



end D1Bound5
end
