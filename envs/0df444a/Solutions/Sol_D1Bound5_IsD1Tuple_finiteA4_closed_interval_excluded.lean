-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.finiteA4_closed_interval_excluded
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:09:53.87831+00:00
-- url     : https://prove2.me/submissions/9a514c3a-2a59-404a-9e53-bae2f314d7a0

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_IsD1Tuple_finiteA4_inequality
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_finite_closed_window_incompatible
import Theorems.Thm_D1Bound5_finite_tuple_root_relative_norm
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5



/-- The whole closed A4 window is excluded for an actual full-ring
subtuple. This also supplies A4 after selecting the b,s,c,d subtuple. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 4 → 𝓞 K) (ht : IsD1Tuple t)
    (hXY : ‖phi (t 0 : K)‖ ≤ ‖phi (t 1 : K)‖)
    (hXC : 1000 ≤ ‖phi (t 0 : K)‖*‖phi (t 2 : K)‖)
    (hC : 200*‖phi (t 1 : K)‖ ≤ ‖phi (t 2 : K)‖)
    (hCD : ‖phi (t 2 : K)‖ ≤ ‖phi (t 3 : K)‖)
    (hleft : 4*165763^2*‖phi (t 1 : K)‖^18*‖phi (t 2 : K)‖^9 /
      (1-1/4000 : ℝ) ≤ ‖phi (t 3 : K)‖)
    (hright : ‖phi (t 3 : K)‖ ≤
      16*‖phi (t 0 : K)‖^10*‖phi (t 2 : K)‖^13 /
        (3969*‖phi (t 1 : K)‖^8*(1+1/4000 : ℝ))) : False := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let X := ‖f (t 0)‖
  let Y := ‖f (t 1)‖
  let C := ‖f (t 2)‖
  let D := ‖f (t 3)‖
  have hX1 : 1 ≤ X := one_le_norm_integer hK phi (ht.2.1 0)
  have hY1 : 1 ≤ Y := one_le_norm_integer hK phi (ht.2.1 1)
  have hXpos : 0 < X := by linarith only [hX1]
  have hYpos : 0 < Y := by linarith only [hY1]
  change 200*Y ≤ C at hC
  change C ≤ D at hCD
  have hC200 : 200 ≤ C := by linarith only [hC,hY1]
  have hCpos : 0 < C := by linarith only [hC200]
  have hCD4000 : 4000 ≤ C*D := by
    have hm := mul_le_mul_of_nonneg_left hCD hCpos.le
    nlinarith only [hm,hC200,sq_nonneg (C-200)]
  obtain ⟨z,hz,hform⟩ := IsD1Tuple.finiteA4_inequality hK phi t ht hXY hXC hC
  let Z := ‖f z‖
  have hZpos : 0 < Z := by
    by_contra h
    have hzero : Z=0 := le_antisymm (le_of_not_gt h) (norm_nonneg (f z))
    change 1 < 165763*Y^9*C^5/Z+(63/8 : ℝ)*Y^4*Z/(X^5*C^7) at hform
    rw [hzero] at hform
    norm_num at hform
  have hzC : (f z)^2=f (t 2)*f (t 3)+1 := by
    simpa only [map_pow,map_mul,map_add,map_one] using congrArg f hz
  obtain ⟨hrootlo,hroothi⟩ := finite_tuple_root_relative_norm
    (f (t 2)) (f (t 3)) (f z) hzC hCD4000
  let U := 165763*Y^9*C^5
  let V := (63/8 : ℝ)*Y^4/(X^5*C^7)
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hform' : 1 < U/Z+V*Z := by
    change 1 < 165763*Y^9*C^5/Z+(63/8 : ℝ)*Y^4*Z/(X^5*C^7) at hform
    convert hform using 1 <;> dsimp [U,V] <;> ring
  have heqlo : 4*U^2/(C*(1-1/4000 : ℝ)) =
      4*165763^2*Y^18*C^9/(1-1/4000 : ℝ) := by
    dsimp [U]
    field_simp [hCpos.ne']
    <;> ring
  have heqhi : 1/(4*V^2*C*(1+1/4000 : ℝ)) =
      16*X^10*C^13/(3969*Y^8*(1+1/4000 : ℝ)) := by
    dsimp [V]
    field_simp [hXpos.ne',hYpos.ne',hCpos.ne']
    <;> ring
  apply finite_closed_window_incompatible C D Z U V (1/4000)
    hCpos hZpos hU hV (by norm_num) (by norm_num) hrootlo hroothi hform'
  · rw [heqlo]
    exact hleft
  · rw [heqhi]
    exact hright

end D1Bound5
end
