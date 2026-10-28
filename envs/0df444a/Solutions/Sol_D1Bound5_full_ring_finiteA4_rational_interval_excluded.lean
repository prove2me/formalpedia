-- Prove2me | solution 1 for D1Bound5.full_ring_finiteA4_rational_interval_excluded
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:50:47.002383+00:00
-- url     : https://prove2.me/submissions/26fad74d-1407-45e0-8742-646b5e2d8b54

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Int.Units
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
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Theorems.Thm_D1Bound5_finiteA4_rational_height
import Theorems.Thm_D1Bound5_full_ring_finiteA4_fixed_interval_of_bounds
import Theorems.Thm_D1Bound5_rationalCutoff_pair_geometry

section
open scoped NumberField
open Module

namespace D1Bound5



/-- The actual A4 window for signed rational anchors. It requires no
coordinate-ring equivalence for the ambient quadratic field. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {S : Finset (𝓞 K)} (hS : IsD1 S) (x y c d : 𝓞 K)
    (hxS : x ∈ S) (hyS : y ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hxy : x ≠ y) (hxc : x ≠ c) (hyc : y ≠ c)
    (hxd : x ≠ d) (hyd : y ≠ d) (hcd : c ≠ d)
    (hC1000 : 1000 ≤ ‖phi (c : K)‖)
    (hCY : 200*‖phi (y : K)‖ ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖)
    (sgn : Bool) (hx : x = if sgn then -1 else 1)
    (hy : y = if sgn then -3 else 3)
    (hleft : 4*(oneSmallCutoffRow_56.M4 : ℝ)^2*‖phi (y : K)‖^18*‖phi (c : K)‖^9/
      (1-1/4000 : ℝ) ≤ ‖phi (d : K)‖)
    (hright : ‖phi (d : K)‖ ≤ ‖phi (c : K)‖^13/
      (4*(oneSmallCutoffRow_56.R4 : ℝ)^2*‖phi (y : K)‖^8*(1+1/4000 : ℝ))) : False := by
  obtain ⟨hX,hY,hdist⟩ := rationalCutoff_pair_geometry phi sgn x y hx hy
  have hXY : ‖phi (x : K)‖ ≤ ‖phi (y : K)‖ := by rw [hX,hY]; norm_num
  have hM : 0 < (oneSmallCutoffRow_56.M4 : ℝ) := by
    exact_mod_cast (show (0 : ℚ) < oneSmallCutoffRow_56.M4 by decide +kernel)
  have hRpos : 0 < (oneSmallCutoffRow_56.R4 : ℝ) := by
    exact_mod_cast (show (0 : ℚ) < oneSmallCutoffRow_56.R4 by decide +kernel)
  have hheight := finiteA4_rational_height phi sgn x y c hx hy hC1000 hCY
  have hdelta : ‖phi (x : K)‖ ≤ ‖phi (x : K)-phi (y : K)‖ := by
    rw [hX,hdist]
    norm_num
  have hR : (6363/409600 : ℝ)*‖phi (x : K)-phi (y : K)‖^8 ≤
      (oneSmallCutoffRow_56.R4 : ℝ)*‖phi (y : K)‖^8 := by
    rw [hdist,hY]
    have hq : (6363/409600 : ℚ)*2^8 ≤ oneSmallCutoffRow_56.R4*3^8 := by decide +kernel
    have hreal := (Rat.cast_le (K := ℝ)).2 hq
    push_cast at hreal
    exact hreal
  exact full_ring_finiteA4_fixed_interval_of_bounds hK phi hS x y c d
    hxS hyS hcS hdS hxy hxc hyc hxd hyd hcd hXY hC1000 hCY hCD
    (oneSmallCutoffRow_56.M4 : ℝ) (oneSmallCutoffRow_56.R4 : ℝ)
    hM hRpos hheight hdelta hR hleft hright







end D1Bound5
end
