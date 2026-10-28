-- Prove2me | solution 1 for D1Bound5.full_ring_finiteN2_inequalities_of_height
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:34.097653+00:00
-- url     : https://prove2.me/submissions/02ebe9b4-7053-4daf-a2f8-9728c0815649

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
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
import Definitions.Def_D1Bound5_FiniteN2IntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_bennett_exists_integral_root_ratio_bound_finite
import Theorems.Thm_D1Bound5_finiteN2RowForm_norm_lt_refined
import Theorems.Thm_D1Bound5_finiteN2_residual_norm_lt
import Theorems.Thm_D1Bound5_finiteN2_residual_norm_lt_point
import Theorems.Thm_D1Bound5_full_ring_finiteN2RowForm_exists_one_le_norm

section
open scoped NumberField
open Module

namespace D1Bound5



/-- Reusable fixed-anchor join. The height premise refers to the actual
integer coefficient polynomials, allowing evaluated coefficient bounds to
feed the same actual root and integral-row construction. Applications must
prove this height premise for their chosen anchors. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {S : Finset (𝓞 K)} (hS : IsD1 S) (x y c d : 𝓞 K)
    (hxS : x ∈ S) (hyS : y ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hxy : x ≠ y) (hxc : x ≠ c) (hyc : y ≠ c)
    (hxd : x ≠ d) (hyd : y ≠ d) (hcd : c ≠ d)
    (hXY : ‖phi (x : K)‖ ≤ ‖phi (y : K)‖)
    (hXC : 1000 ≤ ‖phi (x : K)‖*‖phi (c : K)‖)
    (hCY : 200*‖phi (y : K)‖ ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖)
    (M : ℝ)
    (hheight : ∀ i : Fin 3,
      (101/100 : ℝ)*(‖finiteN2Left (phi (x : K)) (phi (y : K)) (phi (c : K)) i‖+
        ‖finiteN2Right (phi (x : K)) (phi (y : K)) (phi (c : K)) i‖) <
          M*‖phi (y : K)‖^4*‖phi (c : K)‖^2) :
    ∃ z : 𝓞 K, z^2 = c*d+1 ∧
      (1 < M*‖phi (y : K)‖^4*‖phi (c : K)‖^3/‖phi (z : K)‖ +
        (5/4 : ℝ)*‖phi (y : K)‖^2*‖phi (z : K)‖ /
          (‖phi (x : K)‖^3*‖phi (c : K)‖^4)) ∧
      (1 < M*‖phi (y : K)‖^4*‖phi (c : K)‖^3/‖phi (z : K)‖ +
        (101/2560 : ℝ)*max (‖phi (x : K)-phi (y : K)‖^4)
          (‖phi (x : K)‖*‖phi (x : K)-phi (y : K)‖^3)*‖phi (z : K)‖ /
            (‖phi (x : K)‖^3*‖phi (y : K)‖^2*‖phi (c : K)‖^4)) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro a b hab
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hab
  have hnonzero (a : 𝓞 K) (haS : a ∈ S) : f a ≠ 0 := by
    intro h
    apply hS.1 a haS
    apply hf
    simpa only [map_zero] using h
  have hx0 := hnonzero x hxS
  have hy0 := hnonzero y hyS
  have hc0 := hnonzero c hcS
  have hxy0 : f x ≠ f y := fun h => hxy (hf h)
  change ‖f x‖ ≤ ‖f y‖ at hXY
  change 1000 ≤ ‖f x‖*‖f c‖ at hXC
  change 200*‖f y‖ ≤ ‖f c‖ at hCY
  change ‖f c‖ ≤ ‖f d‖ at hCD
  have hXD : ‖f x‖ ≤ ‖f d‖ := by
    have hY := norm_nonneg (f y)
    linarith only [hXY,hCY,hCD,hY]
  have hCDlarge : 1000 ≤ ‖f c‖*‖f d‖ := by
    have hm := mul_le_mul_of_nonneg_right hXD (norm_nonneg (f c))
    nlinarith only [hXC,hm]
  obtain ⟨z,hz⟩ := hS.2 c hcS d hdS hcd
  have hzsq : z^2 = c*d+1 := by simpa only [pow_two] using hz
  have hzC : (f z)^2 = f c*f d+1 := by
    simpa only [map_pow,map_mul,map_add,map_one] using congrArg f hzsq
  have hz0 : f z ≠ 0 := by
    intro hzero
    have heq : f c*f d = -(1 : ℂ) := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa only [hzero,zero_pow (by decide : (2 : ℕ) ≠ 0)] using hzC.symm
    have hn := congrArg norm heq
    simp only [norm_mul,norm_neg,norm_one] at hn
    linarith only [hCDlarge,hn]
  have hzR : z ≠ 0 := by intro hzero; apply hz0; rw [hzero,map_zero]
  obtain ⟨rX,hrX⟩ := hS.2 x hxS c hcS hxc
  obtain ⟨rY,hrY⟩ := hS.2 y hyS c hcS hyc
  obtain ⟨vX,hvX⟩ := hS.2 x hxS d hdS hxd
  obtain ⟨vY,hvY⟩ := hS.2 y hyS d hdS hyd
  have hYC := hXC.trans (mul_le_mul_of_nonneg_right hXY (norm_nonneg (f c)))
  have hCX : 200*‖f x‖ ≤ ‖f c‖ :=
    (mul_le_mul_of_nonneg_left hXY (by norm_num)).trans hCY
  obtain ⟨sX,_,herrX⟩ := bennett_exists_integral_root_ratio_bound_finite
    f x c d z rX vX hx0 hc0 hz0 (by simpa only [pow_two] using hrX)
      (by simpa only [pow_two] using hvX) hzsq hXC hCX
  obtain ⟨sY,_,herrY⟩ := bennett_exists_integral_root_ratio_bound_finite
    f y c d z rY vY hy0 hc0 hz0 (by simpa only [pow_two] using hrY)
      (by simpa only [pow_two] using hvY) hzsq hYC hCY
  have herr (j : Fin 2) :
      ‖(1+1/(![f x,f y] j*f c))^(1/2 : ℂ)-![f sX,f sY] j/(![f x,f y] j*f z)‖ ≤
        (101/100 : ℝ)*‖f c‖/(‖![f x,f y] j‖*‖f z‖^2) := by
    fin_cases j
    · exact herrX.le
    · exact herrY.le
  obtain ⟨i,hi⟩ := full_ring_finiteN2RowForm_exists_one_le_norm
    hK phi x y c z sX sY hxy hzR
  change 1 ≤ ‖finiteN2RowForm (f x) (f y) (f c) (f z) (f sX) (f sY) i‖ at hi
  refine ⟨z,hzsq,?_,?_⟩
  · have h := hi.trans_lt (finiteN2RowForm_norm_lt_refined
      (f x) (f y) (f c) (f z) (f sX) (f sY) hx0 hy0 hz0 i M (hheight i) herr _
      (finiteN2_residual_norm_lt (f x) (f y) (f c) hx0 hy0 hc0 hxy0 hXY hXC i))
    change 1 < M*‖f y‖^4*‖f c‖^3/‖f z‖ +
      (5/4 : ℝ)*‖f y‖^2*‖f z‖/(‖f x‖^3*‖f c‖^4)
    calc
      1 < M*‖f y‖^4*‖f c‖^3/‖f z‖ +
          ((5/4 : ℝ)*‖f y‖^2/(‖f x‖^3*‖f c‖^4))*‖f z‖ := h
      _ = _ := by ring
  · have h := hi.trans_lt (finiteN2RowForm_norm_lt_refined
      (f x) (f y) (f c) (f z) (f sX) (f sY) hx0 hy0 hz0 i M (hheight i) herr _
      (finiteN2_residual_norm_lt_point (f x) (f y) (f c) hx0 hy0 hc0 hxy0 hXY hXC i))
    change 1 < M*‖f y‖^4*‖f c‖^3/‖f z‖ +
      (101/2560 : ℝ)*max (‖f x-f y‖^4) (‖f x‖*‖f x-f y‖^3)*‖f z‖/(‖f x‖^3*‖f y‖^2*‖f c‖^4)
    calc
      1 < M*‖f y‖^4*‖f c‖^3/‖f z‖ +
          ((101/2560 : ℝ)*max (‖f x-f y‖^4) (‖f x‖*‖f x-f y‖^3)/(‖f x‖^3*‖f y‖^2*‖f c‖^4))*‖f z‖ := h
      _ = _ := by ring

end D1Bound5
end
