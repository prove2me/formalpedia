-- Prove2me | solution 1 for D1Bound5.full_ring_finiteN2_rational_interval_excluded
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:49:21.020761+00:00
-- url     : https://prove2.me/submissions/b792a945-3ac1-4fd6-9bc4-5d877b189b77

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
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_finiteN2_rational_height
import Theorems.Thm_D1Bound5_finite_closed_window_incompatible
import Theorems.Thm_D1Bound5_finite_tuple_root_relative_norm
import Theorems.Thm_D1Bound5_full_ring_finiteN2_inequalities_of_height
import Theorems.Thm_D1Bound5_rationalCutoff_pair_geometry

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The N2 closed window for the signed rational pair in any imaginary
quadratic full ring; no Gaussian coordinate model is postulated. -/
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
    (hleft : 4*(oneSmallCutoffRow_56.M2 : ℝ)^2*‖phi (y : K)‖^8*‖phi (c : K)‖^5/
      (1-1/4000 : ℝ) ≤ ‖phi (d : K)‖)
    (hright : ‖phi (d : K)‖ ≤ ‖phi (c : K)‖^7/
      (4*(oneSmallCutoffRow_56.R2 : ℝ)^2*‖phi (y : K)‖^4*(1+1/4000 : ℝ))) : False := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let A := ‖f x‖
  let B := ‖f y‖
  let C := ‖f c‖
  let D := ‖f d‖
  let delta := ‖f x-f y‖
  obtain ⟨hAn,hBn,hdn⟩ := rationalCutoff_pair_geometry phi sgn x y hx hy
  change A=1 at hAn
  change B=3 at hBn
  change delta=2 at hdn
  have hA1 : 1 ≤ A := by rw [hAn]
  have hA : 0 < A := by rw [hAn]; norm_num
  have hB : 0 < B := by rw [hBn]; norm_num
  have hC : 0 < C := by change 1000 ≤ C at hC1000; linarith only [hC1000]
  have hXY : A ≤ B := by rw [hAn,hBn]; norm_num
  change 200*B ≤ C at hCY
  change C ≤ D at hCD
  have hXC : 1000 ≤ A*C := by rw [hAn,one_mul]; exact hC1000
  have hmax : max (delta^4) (A*delta^3) = delta^4 := by rw [hdn,hAn]; norm_num
  have hR2 : (oneSmallCutoffRow_56.R2 : ℝ) = (101/2560 : ℝ)*delta^4/B^4 := by
    rw [hdn,hBn]
    have hq : oneSmallCutoffRow_56.R2 = (101/2560 : ℚ)*2^4/3^4 := by decide +kernel
    have hreal := congrArg (fun q : ℚ => (q : ℝ)) hq
    push_cast at hreal
    exact hreal
  have hRpos : 0 < (oneSmallCutoffRow_56.R2 : ℝ) := by
    exact_mod_cast (show (0 : ℚ) < oneSmallCutoffRow_56.R2 by decide +kernel)
  have hMpos : 0 < (oneSmallCutoffRow_56.M2 : ℝ) := by
    exact_mod_cast (show (0 : ℚ) < oneSmallCutoffRow_56.M2 by decide +kernel)
  have hheight := finiteN2_rational_height phi sgn x y c hx hy hC1000 hCY
  obtain ⟨z,hz,_,hform⟩ := full_ring_finiteN2_inequalities_of_height hK phi hS x y c d
    hxS hyS hcS hdS hxy hxc hyc hxd hyd hcd hXY hXC hCY hCD (oneSmallCutoffRow_56.M2 : ℝ) hheight
  let Z := ‖f z‖
  change 1 < (oneSmallCutoffRow_56.M2 : ℝ)*B^4*C^3/Z+(101/2560 : ℝ)*
    max (delta^4) (A*delta^3)*Z/(A^3*B^2*C^4) at hform
  rw [hmax] at hform
  have hZ : 0 < Z := by
    by_contra h
    have hz0 : Z=0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hz0] at hform
    norm_num at hform
  have hform' : 1 < (oneSmallCutoffRow_56.M2 : ℝ)*B^4*C^3/Z+(oneSmallCutoffRow_56.R2 : ℝ)*B^2*Z/(A^3*C^4) := by
    rw [hR2]
    convert hform using 1 <;> field_simp [hA.ne',hB.ne',hC.ne',hZ.ne'] <;> ring
  have hAD : 4*A ≤ D := by linarith only [hXY,hCY,hCD,hB]
  have hCD4000 : 4000 ≤ C*D := by
    have hm := mul_le_mul_of_nonneg_left hAD hC.le
    nlinarith only [hm,hXC]
  have hzC : (f z)^2 = f c*f d+1 := by
    simpa only [map_pow,map_mul,map_add,map_one] using congrArg f hz
  obtain ⟨hrootlo,hroothi⟩ := finite_tuple_root_relative_norm (f c) (f d) (f z) hzC hCD4000
  let U := (oneSmallCutoffRow_56.M2 : ℝ)*B^4*C^3
  let V := (oneSmallCutoffRow_56.R2 : ℝ)*B^2/(A^3*C^4)
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hf : 1 < U/Z+V*Z := by convert hform' using 1 <;> dsimp [U,V] <;> ring
  have heqlo : 4*U^2/(C*(1-1/4000 : ℝ)) =
      4*(oneSmallCutoffRow_56.M2 : ℝ)^2*B^8*C^5/(1-1/4000 : ℝ) := by
    dsimp [U]
    field_simp [hC.ne']
    <;> ring
  have heqhi : 1/(4*V^2*C*(1+1/4000 : ℝ)) =
      A^6*C^7/(4*(oneSmallCutoffRow_56.R2 : ℝ)^2*B^4*(1+1/4000 : ℝ)) := by
    dsimp [V]
    field_simp [hA.ne',hB.ne',hC.ne',hRpos.ne']
    <;> ring
  apply finite_closed_window_incompatible C D Z U V (1/4000) hC hZ hU hV
    (by norm_num) (by norm_num) hrootlo hroothi hf
  · rw [heqlo]
    exact hleft
  · rw [heqhi]
    apply hright.trans
    have hA6 : 1 ≤ A^6 := by
      have hh : (1 : ℝ)^6 ≤ A^6 := by gcongr
      simpa using hh
    apply div_le_div_of_nonneg_right _ (by positivity)
    change C^7 ≤ A^6*C^7
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA6 (pow_nonneg hC.le 7)

end D1Bound5
end
