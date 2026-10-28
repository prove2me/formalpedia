-- Prove2me | solution 1 for D1Bound5.full_ring_finiteN3_phi_interval_excluded
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:44:35.629982+00:00
-- url     : https://prove2.me/submissions/4c4b4d1c-61ca-417a-91be-f0da7d715ae2

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
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fin.VecNotation
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
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions
import Definitions.Def_D1Bound5_FirstPairGeometry_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_finiteN3_height_scaled
import Theorems.Thm_D1Bound5_full_ring_finiteN3_exact_interval_of_bounds
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
namespace D1Bound5



/-- The normalized relabeled residual is exactly the finite maximum,
including the row with a different power of the anchor separation. -/
theorem firstPairPhi_scaled (b s : ℂ) (hs : s ≠ 0) :
    firstPairPhi b s * ‖s‖^6 = max (‖b-s‖^6) (‖b‖*‖b-s‖^5) := by
  have hS := norm_pos_iff.mpr hs
  unfold firstPairPhi
  rw [max_mul_of_nonneg _ _ (pow_nonneg hS.le 6)]
  congr 1 <;> field_simp [hS.ne'] <;> ring



end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The relabeled N3 window uses its actual separation-dependent
residual and the uniform coefficient4143; no fixed third-row premise. -/
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
    (hleft : (commonWindowN3 ‖phi (x : K)‖ ‖phi (y : K)‖ ‖phi (c : K)‖
      4143 ((3535/409600 : ℝ)*firstPairPhi (phi (x : K)) (phi (y : K)))).1 ≤ ‖phi (d : K)‖)
    (hright : ‖phi (d : K)‖ ≤
      (commonWindowN3 ‖phi (x : K)‖ ‖phi (y : K)‖ ‖phi (c : K)‖
        4143 ((3535/409600 : ℝ)*firstPairPhi (phi (x : K)) (phi (y : K)))).2) : False := by
  let X := phi (x : K)
  let Y := phi (y : K)
  let C := ‖phi (c : K)‖
  have hY1 : 1 ≤ ‖Y‖ := one_le_norm_integer hK phi (hS.1 y hyS)
  have hY : 0 < ‖Y‖ := by linarith only [hY1]
  have hy0 : Y ≠ 0 := norm_pos_iff.mp hY
  have hsep : X-Y ≠ 0 := sub_ne_zero.mpr (fun hh => hxy
    (Subtype.ext (phi.injective hh)))
  have hd : 0 < ‖X-Y‖ := norm_pos_iff.mpr hsep
  have hPhi : 0 < firstPairPhi X Y := by
    apply lt_of_lt_of_le (pow_pos (div_pos hd hY) 6)
    exact le_max_left _ _
  change 1000 ≤ C at hC1000
  have hYC : 1000 ≤ ‖Y‖*C := by
    have hC : 0 ≤ C := norm_nonneg _
    nlinarith only [hY1,hC1000,hC]
  have hheight (i : Fin 3) := finiteN3_height_scaled X Y (phi (c : K)) hy0 hXY hYC i
  have hR : (3535/409600 : ℝ)*max (‖X-Y‖^6) (‖X‖*‖X-Y‖^5) ≤
      ((3535/409600 : ℝ)*firstPairPhi X Y)*‖Y‖^6 := by
    rw [mul_assoc,firstPairPhi_scaled X Y hy0]
  exact full_ring_finiteN3_exact_interval_of_bounds hK phi hS x y c d
    hxS hyS hcS hdS hxy hxc hyc hxd hyd hcd hXY hC1000 hCY hCD
    4143 ((3535/409600 : ℝ)*firstPairPhi X Y) (by norm_num)
    (by positivity) hheight hR hleft hright

end D1Bound5
end
