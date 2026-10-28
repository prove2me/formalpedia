-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.ordinary_tail_incompatible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:58:31.514016+00:00
-- url     : https://prove2.me/submissions/37fca716-d80d-4693-986f-fcb02cff135b

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OrdinaryClosedIntervals_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_ordinary_closed_interval_excluded
import Theorems.Thm_D1Bound5_forbidden_interval_chain
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
namespace D1Bound5



/-- Positive geometric lower endpoints tend beyond every fixed candidate.
This is an all-orders argument, not a finite sample of interval checks. -/
theorem scaled_power_unbounded (c a x : ℝ) (hc : 0 < c) (ha : 1 < a) :
    ∃ n : ℕ, x < c*a^n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x/c) ha
  refine ⟨n, ?_⟩
  have h := (div_lt_iff₀ hc).mp hn
  simpa only [mul_comm] using h





end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5







theorem ordinaryWindowLower_succ (B C : ℝ) (k : ℕ) :
    ordinaryWindowLower B C (k+1) = ordinaryWindowLower B C k*(42*B^3*C)^2 := by
  unfold ordinaryWindowLower
  rw [Nat.mul_add,pow_add]
  ring

theorem ordinaryWindowUpper_succ (A B C : ℝ) (k : ℕ) :
    ordinaryWindowUpper A B C (k+1) =
      ordinaryWindowUpper A B C k*(2*A*C^2/(5*B))^2 := by
  unfold ordinaryWindowUpper
  rw [Nat.mul_add,pow_add]
  ring

/-- The ordinary tail is genuinely infinite. A single checked overlap
at orders 5 and 6 propagates because the actual quadratic lower rate
exceeds the height rate; geometric lower endpoints are unbounded. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 4 → 𝓞 K) (ht : IsD1Tuple t)
    (hAB : ‖phi (t 0 : K)‖ ≤ ‖phi (t 1 : K)‖)
    (hAC : 1000 ≤ ‖phi (t 0 : K)‖*‖phi (t 2 : K)‖)
    (hC : 4*‖phi (t 1 : K)‖ < ‖phi (t 2 : K)‖)
    (hCD : ‖phi (t 2 : K)‖ ≤ ‖phi (t 3 : K)‖)
    (hrate : 42*‖phi (t 1 : K)‖^3*‖phi (t 2 : K)‖ <
      2*‖phi (t 0 : K)‖*‖phi (t 2 : K)‖^2/(5*‖phi (t 1 : K)‖))
    (hoverlap : ordinaryWindowLower ‖phi (t 1 : K)‖ ‖phi (t 2 : K)‖ 6 ≤
      ordinaryWindowUpper ‖phi (t 0 : K)‖ ‖phi (t 1 : K)‖ ‖phi (t 2 : K)‖ 5)
    (hstart : ordinaryWindowLower ‖phi (t 1 : K)‖ ‖phi (t 2 : K)‖ 5 ≤
      ‖phi (t 3 : K)‖) : False := by
  let A := ‖phi (t 0 : K)‖
  let B := ‖phi (t 1 : K)‖
  let C := ‖phi (t 2 : K)‖
  let D := ‖phi (t 3 : K)‖
  let H := 42*B^3*C
  let R := 2*A*C^2/(5*B)
  have hA1 : 1 ≤ A := one_le_norm_integer hK phi (ht.2.1 0)
  have hA0 : 0 < A := by linarith only [hA1]
  have hB1 : 1 ≤ B := one_le_norm_integer hK phi (ht.2.1 1)
  have hB0 : 0 < B := by linarith only [hB1]
  have hC1 : 1 < C := by change 4*B<C at hC; linarith only [hC,hB1]
  have hC0 : 0 < C := lt_trans (by norm_num) hC1
  have hH1 : 1 < H := by
    have hB3 : 1 ≤ B^3 := by
      calc
        (1 : ℝ) = 1^3 := by norm_num
        _ ≤ B^3 := by gcongr
    have hh := mul_le_mul_of_nonneg_right hB3 hC0.le
    dsimp [H]
    linarith only [hh,hC1]
  have hH0 : 0 < H := lt_trans (by norm_num) hH1
  change H < R at hrate
  have hR0 : 0 < R := hH0.trans hrate
  have hHR : H^2 ≤ R^2 := by gcongr
  have hpos (k : ℕ) : 0 < ordinaryWindowUpper A B C k := by
    unfold ordinaryWindowUpper
    positivity
  have hov (n : ℕ) : ordinaryWindowLower B C (n+6) ≤ ordinaryWindowUpper A B C (n+5) := by
    induction n with
    | zero => exact hoverlap
    | succ n ih =>
      rw [show n+1+6=(n+6)+1 by omega, show n+1+5=(n+5)+1 by omega,
        ordinaryWindowLower_succ,ordinaryWindowUpper_succ]
      exact (mul_le_mul_of_nonneg_right ih (sq_nonneg H)).trans
        (mul_le_mul_of_nonneg_left hHR (hpos _).le)
  have hgeom (n : ℕ) : ordinaryWindowLower B C (n+5) = ordinaryWindowLower B C 5*(H^2)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show n+1+5=(n+5)+1 by omega,ordinaryWindowLower_succ,ih,pow_succ]
      ring
  have hbase : 0 < ordinaryWindowLower B C 5 := by
    unfold ordinaryWindowLower
    positivity
  have hHsquared : 1 < H^2 := by nlinarith only [hH1,sq_nonneg (H-1)]
  apply forbidden_interval_chain (fun n => ordinaryWindowLower B C (n+5))
    (fun n => ordinaryWindowUpper A B C (n+5)) D hstart
  · intro n
    convert hov n using 1 <;> congr 1 <;> omega
  · intro n hn
    exact IsD1Tuple.ordinary_closed_interval_excluded hK phi t ht
      hAB hAC hC hCD (n+5) (by omega) hn.1 hn.2
  · obtain ⟨n,hn⟩ := scaled_power_unbounded (ordinaryWindowLower B C 5) (H^2) D hbase hHsquared
    exact ⟨n,by rw [hgeom]; exact hn⟩

end D1Bound5
end
