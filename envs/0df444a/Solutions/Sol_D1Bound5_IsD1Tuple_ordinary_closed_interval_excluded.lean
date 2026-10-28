-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.ordinary_closed_interval_excluded
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:21:08.267112+00:00
-- url     : https://prove2.me/submissions/537c97f5-188d-4d97-b7c1-31c74d4b7dfd

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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
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
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OrdinaryClosedIntervals_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_bennettTwoResidualRate_norm_lower
import Theorems.Thm_D1Bound5_finite_closed_window_incompatible
import Theorems.Thm_D1Bound5_finite_tuple_root_relative_norm
import Theorems.Thm_D1Bound5_full_ring_bennett_two_integer_k
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5





/-- Every positive-order ordinary window is excluded by the actual
integral Bennett form. The quadratic residual rate is derived from the
actual node separation, and the terminal square root is supplied by the
tuple. No approximation bound or list of orders is assumed. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 4 → 𝓞 K) (ht : IsD1Tuple t)
    (hAB : ‖phi (t 0 : K)‖ ≤ ‖phi (t 1 : K)‖)
    (hAC : 1000 ≤ ‖phi (t 0 : K)‖*‖phi (t 2 : K)‖)
    (hC : 4*‖phi (t 1 : K)‖ < ‖phi (t 2 : K)‖)
    (hCD : ‖phi (t 2 : K)‖ ≤ ‖phi (t 3 : K)‖)
    (k : ℕ) (hk : 1 ≤ k)
    (hleft : ordinaryWindowLower ‖phi (t 1 : K)‖ ‖phi (t 2 : K)‖ k ≤
      ‖phi (t 3 : K)‖)
    (hright : ‖phi (t 3 : K)‖ ≤
      ordinaryWindowUpper ‖phi (t 0 : K)‖ ‖phi (t 1 : K)‖ ‖phi (t 2 : K)‖ k) :
    False := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let A := ‖f (t 0)‖
  let B := ‖f (t 1)‖
  let C := ‖f (t 2)‖
  let D := ‖f (t 3)‖
  let H := 42*B^3*C
  let R := 2*A*C^2/(5*B)
  have hA1 : 1 ≤ A := one_le_norm_integer hK phi (ht.2.1 0)
  have hB1 : 1 ≤ B := one_le_norm_integer hK phi (ht.2.1 1)
  have hA0 : 0 < A := by linarith only [hA1]
  have hB0 : 0 < B := by linarith only [hB1]
  change A ≤ B at hAB
  change 1000 ≤ A*C at hAC
  change 4*B < C at hC
  change C ≤ D at hCD
  have hC0 : 0 < C := by linarith only [hC,hB0]
  have hH : 0 < H := by dsimp [H]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hAD : 4*A ≤ D := by linarith only [hAB,hC,hCD]
  have hCD4000 : 4000 ≤ C*D := by
    have hm := mul_le_mul_of_nonneg_left hAD hC0.le
    nlinarith only [hm,hAC]
  obtain ⟨rA,hrA⟩ := ht.2.2 0 2 (by decide)
  obtain ⟨rB,hrB⟩ := ht.2.2 1 2 (by decide)
  obtain ⟨vA,hvA⟩ := ht.2.2 0 3 (by decide)
  obtain ⟨vB,hvB⟩ := ht.2.2 1 3 (by decide)
  obtain ⟨z,hz⟩ := ht.2.2 2 3 (by decide)
  have hz' : z^2=t 2*t 3+1 := by simpa only [pow_two] using hz
  have hform := full_ring_bennett_two_integer_k hK phi
    (t 0) (t 1) (t 2) (t 3) rA rB vA vB z
    (ht.2.1 0) (ht.2.1 1) (ht.2.1 2) (ht.2.1 3)
    (ht.1.ne (by decide : (0 : Fin 4) ≠ 1))
    (by simpa only [pow_two] using hrA) (by simpa only [pow_two] using hrB)
    (by simpa only [pow_two] using hvA) (by simpa only [pow_two] using hvB)
    hz' hAB hAC hC k hk
  let Z := ‖f z‖
  let Ractual := bennettTwoResidualRate A B C ‖f (t 0)-f (t 1)‖
  change 1 < 3*C*H^k/(B*Z)+Z/(2*Ractual^k) at hform
  have hZ : 0 < Z := by
    by_contra h
    have hzero : Z=0 := le_antisymm (le_of_not_gt h) (norm_nonneg (f z))
    rw [hzero] at hform
    norm_num at hform
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hr : R < Ractual := bennettTwoResidualRate_norm_lower
    (f (t 0)) (f (t 1)) (f (t 2))
    (norm_pos_iff.mp hA0) (norm_pos_iff.mp hB0)
    (hf.ne (ht.1.ne (by decide : (0 : Fin 4) ≠ 1))) hAB hAC
  have hpow : R^k ≤ Ractual^k := by gcongr
  have hres : Z/(2*Ractual^k) ≤ Z/(2*R^k) :=
    div_le_div_of_nonneg_left hZ.le (by positivity)
      (mul_le_mul_of_nonneg_left hpow (by norm_num))
  let U := 3*C*H^k/B
  let V := 1/(2*R^k)
  have hform' : 1 < U/Z+V*Z := by
    have hh := hform.trans_le (add_le_add le_rfl hres)
    calc
      1 < 3*C*H^k/(B*Z)+Z/(2*R^k) := hh
      _ = U/Z+V*Z := by
        dsimp only [U,V]
        ring
  have hzC : (f z)^2=f (t 2)*f (t 3)+1 := by
    simpa only [map_pow,map_mul,map_add,map_one] using congrArg f hz'
  obtain ⟨hrootlo,hroothi⟩ := finite_tuple_root_relative_norm
    (f (t 2)) (f (t 3)) (f z) hzC hCD4000
  have heqlo : 4*U^2/(C*(1-1/4000 : ℝ)) = ordinaryWindowLower B C k := by
    dsimp [U,ordinaryWindowLower,H]
    rw [Nat.mul_comm 2 k,pow_mul]
    field_simp [hB0.ne',hC0.ne']
    <;> ring
  have heqhi : 1/(4*V^2*C*(1+1/4000 : ℝ)) = ordinaryWindowUpper A B C k := by
    dsimp [V,ordinaryWindowUpper]
    change 1/(4*(1/(2*R^k))^2*C*(1+1/4000 : ℝ)) = R^(2*k)/(C*(1+1/4000 : ℝ))
    rw [Nat.mul_comm 2 k,pow_mul]
    field_simp [hR.ne',hC0.ne']
    <;> ring
  apply finite_closed_window_incompatible C D Z U V (1/4000)
    hC0 hZ (by dsimp [U]; positivity) (by dsimp [V]; positivity)
    (by norm_num) (by norm_num) hrootlo hroothi hform'
  · rw [heqlo]
    exact hleft
  · rw [heqhi]
    exact hright







end D1Bound5
end
