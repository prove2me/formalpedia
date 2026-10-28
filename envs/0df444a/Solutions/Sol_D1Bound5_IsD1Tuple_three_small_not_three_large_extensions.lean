-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.three_small_not_three_large_extensions
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:53:08.667428+00:00
-- url     : https://prove2.me/submissions/48f3d644-090c-4a29-b6e5-f5d159cd600f

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
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Definitions.Def_D1Bound5_TwoSmallHeightScalar_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_three_small_pair_at
import Theorems.Thm_D1Bound5_IsD1Tuple_two_small_ordinary_at
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_ordinary_height_power_upper
import Theorems.Thm_D1Bound5_three_small_three_large_impossible

section
open scoped NumberField
open Module

namespace D1Bound5









/-- Three extensions above10^40 are impossible for a fixed actual
small triple. All three pair alternatives and the ordinary upper bound
are supplied by restrictions of the sextuple. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hS : ‖phi (a 2 : K)‖ < 3) (hU : (10 : ℝ)^40 ≤ ‖phi (a 3 : K)‖) : False := by
  have hU1000 : 1000 ≤ ‖phi (a 3 : K)‖ := by norm_num at hU; linarith only [hU]
  have hV1000 : 1000 ≤ ‖phi (a 4 : K)‖ := hU1000.trans (hmon (by decide))
  have hUV := ha.three_small_pair_at hK phi a hmon hS 3 4 (by decide) (by decide) hU1000
  have hVW := ha.three_small_pair_at hK phi a hmon hS 4 5 (by decide) (by decide) hV1000
  have hUW := ha.three_small_pair_at hK phi a hmon hS 3 5 (by decide) (by decide) hU1000
  have hB3 := (hmon (by decide : (1 : Fin 6) ≤ 2)).trans_lt hS
  have hU8 : (10 : ℝ)^8 ≤ ‖phi (a 3 : K)‖ := by norm_num at hU ⊢; linarith only [hU]
  have hW : 0 < ‖phi (a 5 : K)‖ := by
    have hh := one_le_norm_integer hK phi (ha.2.1 5)
    linarith only [hh]
  have hheight := ha.two_small_ordinary_at hK phi a hmon hB3 3 (by decide) (by decide) hU8
  have hupper := ordinary_height_power_upper _ _ hU hW hheight
  exact three_small_three_large_impossible _ _ _ hU hUV hVW hUW hupper

end D1Bound5
end
