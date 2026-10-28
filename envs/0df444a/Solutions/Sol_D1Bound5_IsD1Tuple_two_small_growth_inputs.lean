-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.two_small_growth_inputs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:27:25.120456+00:00
-- url     : https://prove2.me/submissions/6a8fc5e2-8688-4a0c-9219-48712ca77224

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_IsD1Tuple_comp_injective_map
import Theorems.Thm_D1Bound5_IsD1Tuple_crossBlock_growth
import Theorems.Thm_D1Bound5_IsD1Tuple_productFour_large_growth
import Theorems.Thm_D1Bound5_IsD1Tuple_productFour_mixed_growth
import Theorems.Thm_D1Bound5_crossBlock_growth
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5



/-- The determinant growth inputs for the two-small cutoff, with roots
and all subtuple restrictions obtained from the sextuple itself. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hS : 3 ≤ ‖phi (a 2 : K)‖) :
    (3/8 : ℝ)*‖phi (a 0 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖ < ‖phi (a 4 : K)‖ ∧
    2*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖*‖phi (a 4 : K)‖ < ‖phi (a 5 : K)‖ ∧
    (9 ≤ ‖phi (a 0 : K)‖*‖phi (a 3 : K)‖ →
      ‖phi (a 0 : K)‖^3*‖phi (a 1 : K)‖*‖phi (a 3 : K)‖^3*‖phi (a 4 : K)‖/
        (7*‖phi (a 2 : K)‖) < ‖phi (a 5 : K)‖) := by
  let b : Fin 4 → 𝓞 K := fun i => a (![0,2,3,4] i)
  let c : Fin 4 → 𝓞 K := fun i => a (![2,3,4,5] i)
  have hb := ha.comp_injective_map a (![0,2,3,4])
    (by decide : Function.Injective (![0,2,3,4] : Fin 4 → Fin 6))
  have hc := ha.comp_injective_map a (![2,3,4,5])
    (by decide : Function.Injective (![2,3,4,5] : Fin 4 → Fin 6))
  have hbmon : Monotone (fun i => ‖phi (b i : K)‖) := by
    have hidx : Monotone (![0,2,3,4] : Fin 4 → Fin 6) := by decide
    exact fun i j hij => hmon (hidx hij)
  have hcmon : Monotone (fun i => ‖phi (c i : K)‖) := by
    have hidx : Monotone (![2,3,4,5] : Fin 4 → Fin 6) := by decide
    exact fun i j hij => hmon (hidx hij)
  have hA : 1 ≤ ‖phi (a 0 : K)‖ := one_le_norm_integer hK phi (ha.2.1 0)
  have hfirst := hb.productFour_mixed_growth hK phi b hbmon hA hS
  have hsecond := hc.productFour_large_growth hK phi c hcmon hS
  have hA0 : 0 < ‖phi (a 0 : K)‖ := by linarith only [hA]
  have hS0 : 0 < ‖phi (a 2 : K)‖ := by linarith only [hS]
  have hT0 : 0 < ‖phi (a 3 : K)‖ := hS0.trans_le (hmon (by decide))
  refine ⟨?_,hsecond,?_⟩
  · change (3/2 : ℝ)*‖phi (a 0 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖ <
      ‖phi (a 4 : K)‖ at hfirst
    have hp : 0 < ‖phi (a 0 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖ := by positivity
    nlinarith only [hfirst,hp]
  · intro hlarge
    let p : Fin 3 ↪ Fin 6 := ⟨![0,1,2],by decide⟩
    let q : Fin 3 ↪ Fin 6 := ⟨![3,4,5],by decide⟩
    have hpm : Monotone (fun i => ‖phi (a (p i) : K)‖) := by
      have hidx : Monotone (![0,1,2] : Fin 3 → Fin 6) := by decide
      exact fun i j hij => hmon (hidx hij)
    have hqm : Monotone (fun i => ‖phi (a (q i) : K)‖) := by
      have hidx : Monotone (![3,4,5] : Fin 3 → Fin 6) := by decide
      exact fun i j hij => hmon (hidx hij)
    have hh := ha.crossBlock_growth hK phi a p q
      (by intro i j; fin_cases i <;> fin_cases j <;> decide) hpm hqm hlarge
    apply (div_lt_iff₀ (by positivity : 0 < 7*‖phi (a 2 : K)‖)).2
    change (‖phi (a 0 : K)‖*‖phi (a 3 : K)‖)^3*
      (‖phi (a 1 : K)‖*‖phi (a 4 : K)‖)/7 <
        ‖phi (a 2 : K)‖*‖phi (a 5 : K)‖ at hh
    nlinarith only [hh]



end D1Bound5
end
