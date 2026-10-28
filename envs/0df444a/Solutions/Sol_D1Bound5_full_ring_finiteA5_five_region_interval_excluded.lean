-- Prove2me | solution 1 for D1Bound5.full_ring_finiteA5_five_region_interval_excluded
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:53:25.657559+00:00
-- url     : https://prove2.me/submissions/2a416c1b-9854-488f-9a59-75aadc9d245f

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
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
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_CommonIntervalWindows_Definitions
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA5RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Definitions.Def_D1Bound5_FiveRegionParameters_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_finiteA5_height_five_regions
import Theorems.Thm_D1Bound5_fiveRegionAnchorRatio_nonneg
import Theorems.Thm_D1Bound5_fiveRegion_distance_rates
import Theorems.Thm_D1Bound5_full_ring_finiteA5_max_interval_of_bounds
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5

/-- Actual A5 window in each of the five first-pair regions. Its height
and residual inputs are proved here from the displayed matrix and the
actual anchor ratio. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {S : Finset (𝓞 K)} (hS : IsD1 S) (x y c d : 𝓞 K)
    (hxS : x ∈ S) (hyS : y ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hxy : x ≠ y) (hxc : x ≠ c) (hyc : y ≠ c)
    (hxd : x ≠ d) (hyd : y ≠ d) (hcd : c ≠ d)
    (hXY : ‖phi (x : K)‖ ≤ ‖phi (y : K)‖)
    (hC1000 : 1000 ≤ ‖phi (c : K)‖)
    (hCY : 200*‖phi (y : K)‖ ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖)
    (r : Fin 5) (hratio : ‖phi (x : K)‖ ≤ fiveRegionAnchorRatio r*‖phi (y : K)‖)
    (hleft : (commonWindowA5 ‖phi (x : K)‖ ‖phi (y : K)‖ ‖phi (c : K)‖
      (fiveRegionA5Height r) (fiveRegionA5Residual r)).1 ≤ ‖phi (d : K)‖)
    (hright : ‖phi (d : K)‖ ≤
      (commonWindowA5 ‖phi (x : K)‖ ‖phi (y : K)‖ ‖phi (c : K)‖
        (fiveRegionA5Height r) (fiveRegionA5Residual r)).2) : False := by
  have hY1 := one_le_norm_integer hK phi (hS.1 y hyS)
  have hY : 0 < ‖phi (y : K)‖ := by linarith only [hY1]
  have hYC : 1000 ≤ ‖phi (y : K)‖*‖phi (c : K)‖ := by
    nlinarith only [hY1,hC1000,norm_nonneg (phi (c : K))]
  have hheight (i : Fin 3) := finiteA5_height_five_regions r
    (phi (x : K)) (phi (y : K)) (phi (c : K)) (norm_pos_iff.mp hY) hratio hYC i
  have hR := (fiveRegion_distance_rates r (phi (x : K)) (phi (y : K)) hratio).2.2.2.2
  have hMpos : 0 < fiveRegionA5Height r := by fin_cases r <;> norm_num [fiveRegionA5Height]
  have hRpos : 0 < fiveRegionA5Residual r := by
    unfold fiveRegionA5Residual
    have hh := fiveRegionAnchorRatio_nonneg r
    positivity
  exact full_ring_finiteA5_max_interval_of_bounds hK phi hS x y c d
    hxS hyS hcS hdS hxy hxc hyc hxd hyd hcd hXY hC1000 hCY hCD
    (fiveRegionA5Height r) (fiveRegionA5Residual r) hMpos hRpos hheight hR hleft hright

end D1Bound5
end
