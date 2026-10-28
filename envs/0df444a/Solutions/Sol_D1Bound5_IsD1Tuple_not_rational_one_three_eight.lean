-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.not_rational_one_three_eight
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:19:46.600803+00:00
-- url     : https://prove2.me/submissions/628f99f3-67a2-4702-8234-71fd7e217ca5

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
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
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_Regular_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_rational_cutoff_fourth_norm_sq_lt
import Theorems.Thm_D1Bound5_IsD1Tuple_tail_irregular_and_growth

section
open scoped NumberField Classical
open Module

namespace D1Bound5





/-- For the remaining rational triple (1,3,8), the analytic cutoff N(t)<1024
already contradicts the strict tail-growth inequality T>48. -/
theorem one_three_eight_cutoff_contradiction (T : ℝ)
    (hcutoff : T^2 < 1024) (hgrowth : 48 < T) : False := by
  nlinarith

end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The universal rational triple cannot start a sorted full-ring
sextuple: its actual analytic cutoff contradicts actual tail growth. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (sgn : Bool)
    (h0 : a 0 = if sgn then -1 else 1)
    (h1 : a 1 = if sgn then -3 else 3)
    (h2 : a 2 = if sgn then -8 else 8) : False := by
  have hcut := IsD1Tuple.rational_cutoff_fourth_norm_sq_lt
    hK phi a ha hmon sgn h0 h1 h2
  let b : Fin 4 → 𝓞 K := fun i => a (Fin.castAdd 2 i)
  have hi : Function.Injective (Fin.castAdd 2 : Fin 4 → Fin 6) := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun k : Fin 6 => k.val) h
  have hb : IsD1Tuple b := by
    refine ⟨ha.1.comp hi,?_,?_⟩
    · intro i
      exact ha.2.1 (Fin.castAdd 2 i)
    · intro i j hij
      exact ha.2.2 (Fin.castAdd 2 i) (Fin.castAdd 2 j) (hi.ne hij)
  have hm : Monotone (fun i => ‖phi (b i : K)‖) := by
    intro i j hij
    exact hmon hij
  have hB : ‖phi (a 1 : K)‖ = 3 := by rw [h1]; cases sgn <;> norm_num [NumberField.RingOfIntegers.coe_eq_algebraMap,map_ofNat]
  have hS : ‖phi (a 2 : K)‖ = 8 := by rw [h2]; cases sgn <;> norm_num [NumberField.RingOfIntegers.coe_eq_algebraMap,map_ofNat]
  have hB3 : 3 ≤ ‖phi (b 1 : K)‖ := by change 3 ≤ ‖phi (a 1 : K)‖; rw [hB]
  have hg := (IsD1Tuple.tail_irregular_and_growth hK phi b hb hm hB3).2
  change 2*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖ at hg
  rw [hB,hS] at hg
  exact one_three_eight_cutoff_contradiction ‖phi (a 3 : K)‖ hcut (by norm_num at hg ⊢; exact hg)

end D1Bound5
end
