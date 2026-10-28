-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.small_norm_retained_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:44:38.170489+00:00
-- url     : https://prove2.me/submissions/51ee9061-7fda-4312-92bb-9dacba4009e5

import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_IsD1Tuple_frontier_small_norm_growth
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- The five actual small-norm frontier rows give both the factor-two
frontier and AT≥48 needed by the analytic retained argument. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hN8 : ‖phi (a 0 : K)‖^2 ≤ 8) (hB : 3 ≤ ‖phi (a 1 : K)‖)
    (hcase :
      (‖phi (a 0 : K)‖^2 = 1 ∧ 8 ≤ ‖phi (a 1 : K)‖) ∨
      (‖phi (a 0 : K)‖^2 = 2 ∧ 4 ≤ ‖phi (a 1 : K)‖) ∨
      ‖phi (a 0 : K)‖^2 = 3 ∨ ‖phi (a 0 : K)‖^2 = 4 ∨
      5 ≤ ‖phi (a 0 : K)‖^2) :
    2*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖ ∧
      48 ≤ ‖phi (a 0 : K)‖*‖phi (a 3 : K)‖ := by
  let A := ‖phi (a 0 : K)‖
  let B := ‖phi (a 1 : K)‖
  let S := ‖phi (a 2 : K)‖
  let T := ‖phi (a 3 : K)‖
  have hA : 1 ≤ A := one_le_norm_integer hK phi (ha.2.1 0)
  have hBS : B ≤ S := hmon (by decide : (1 : Fin 4) ≤ 2)
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hB]
  have hS0 : 0 < S := hB0.trans_le hBS
  have hpos : 0 < A*B*S := by positivity
  have hrows := IsD1Tuple.frontier_small_norm_growth hK phi a ha hmon hN8
  have hfront : 2*A*B*S < T := by
    rcases hcase with ⟨hN,hBB⟩ | ⟨hN,hBB⟩ | hN | hN | hN
    · have hh := hrows.1 hN hBB
      nlinarith only [hh,hpos]
    · have hh := hrows.2.1 hN hBB
      nlinarith only [hh,hpos]
    · have hh := hrows.2.2.1 hN hB
      nlinarith only [hh,hpos]
    · have hh := hrows.2.2.2.1 hN hB
      nlinarith only [hh,hpos]
    · have hh := hrows.2.2.2.2 hN hB
      nlinarith only [hh,hpos]
  have hBsq : (9 : ℝ) ≤ B^2 := by nlinarith only [hB,sq_nonneg (B-3)]
  have hAB27 : 27 ≤ A^2*B^2 := by
    rcases hcase with ⟨hN,hBB⟩ | ⟨hN,hBB⟩ | hN | hN | hN
    · change A^2 = 1 at hN
      rw [hN]
      nlinarith only [hBB,sq_nonneg (B-8)]
    · change A^2 = 2 at hN
      rw [hN]
      nlinarith only [hBB,sq_nonneg (B-4)]
    · change A^2 = 3 at hN
      rw [hN]
      nlinarith only [hBsq]
    · change A^2 = 4 at hN
      rw [hN]
      nlinarith only [hBsq]
    · have hh := mul_le_mul hN hBsq (by norm_num : (0 : ℝ) ≤ 9) (sq_nonneg A)
      nlinarith only [hh]
  have hBS' := mul_le_mul_of_nonneg_left hBS (by positivity : 0 ≤ A^2*B)
  have hfront' := mul_lt_mul_of_pos_left hfront hA0
  exact ⟨hfront,by nlinarith only [hAB27,hBS',hfront']⟩



end D1Bound5
end
