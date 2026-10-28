-- Prove2me | solution 1 for D1Bound5.full_ring_finiteP_adaptive_closed_interval_excluded
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:47:11.475015+00:00
-- url     : https://prove2.me/submissions/3606cb83-1018-4fe7-9165-701f976ec54f

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
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
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePAdaptiveResidual_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_finitePAdaptiveRate_pos
import Theorems.Thm_D1Bound5_finite_closed_window_incompatible
import Theorems.Thm_D1Bound5_finite_tuple_root_relative_norm
import Theorems.Thm_D1Bound5_full_ring_finiteP_adaptive_inequality
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The full closed finite P window, using the same
relative root error 1/4000 as the neighboring finite families. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {S : Finset (𝓞 K)} (hS : IsD1 S) (a : Fin 3 → 𝓞 K) (c d : 𝓞 K)
    (haS : ∀ j, a j ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hinj : Function.Injective a) (hac : ∀ j, a j ≠ c)
    (had : ∀ j, a j ≠ d) (hcd : c ≠ d)
    (hmon : Monotone (fun j => ‖phi (a j : K)‖))
    (hCT : 200*‖phi (a 2 : K)‖ ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖)
    (hAC : 1000 ≤ ‖phi (a 0 : K)‖*‖phi (c : K)‖)
    (q : ℝ) (hq : 1 ≤ q) (hqab : q*‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖)
    (hleft : 4*(2400 : ℝ)^2*
      (max (‖phi (a 1 : K)‖*‖phi (a 2 : K)‖^3)
        (‖phi (a 1 : K)‖^3*‖phi (a 2 : K)‖^2))^2*
      ‖phi (c : K)‖^5/(1-1/4000 : ℝ) ≤ ‖phi (d : K)‖)
    (hright : ‖phi (d : K)‖ ≤ ‖phi (a 0 : K)‖^6*‖phi (c : K)‖^9/
      (4*(finitePAdaptiveRate (1/q))^2*‖phi (a 2 : K)‖^4*(1+1/4000 : ℝ))) : False := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let A := ‖f (a 0)‖
  let B := ‖f (a 1)‖
  let T := ‖f (a 2)‖
  let C := ‖f c‖
  let D := ‖f d‖
  let H := max (B*T^3) (B^3*T^2)
  change 200*T ≤ C at hCT
  change C ≤ D at hCD
  change 1000 ≤ A*C at hAC
  have hn (j : Fin 3) : 1 ≤ ‖f (a j)‖ := one_le_norm_integer hK phi (hS.1 _ (haS j))
  have hA : 0 < A := by have hh := hn 0; linarith only [hh]
  have hB : 0 < B := by have hh := hn 1; linarith only [hh]
  have hT : 0 < T := by have hh := hn 2; linarith only [hh]
  have hC : 0 < C := by linarith only [hCT,hT]
  have hAT : A ≤ T := hmon (by decide)
  have hAD : 4*A ≤ D := by linarith only [hAT,hCT,hCD,hT]
  have hCD4000 : 4000 ≤ C*D := by
    have hh := mul_le_mul_of_nonneg_left hAD hC.le
    nlinarith only [hh,hAC]
  obtain ⟨z,hz,hform⟩ := full_ring_finiteP_adaptive_inequality hK phi hS a c d
    haS hcS hdS hinj hac had hcd hmon hCT hCD hAC q hq hqab
  let Z := ‖f z‖
  have hZ : 0 < Z := by
    by_contra h
    have hzero : Z = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg (f z))
    change 1 < 2400*H*C^3/Z+finitePAdaptiveRate (1/q)*T^2*Z/(A^3*C^5) at hform
    rw [hzero] at hform
    norm_num at hform
  have hzC : (f z)^2 = f c*f d+1 := by
    simpa only [map_pow,map_mul,map_add,map_one] using congrArg f hz
  obtain ⟨hlo,hhi⟩ := finite_tuple_root_relative_norm (f c) (f d) (f z) hzC hCD4000
  let U := (2400 : ℝ)*H*C^3
  let V := finitePAdaptiveRate (1/q)*T^2/(A^3*C^5)
  have hq0 : 0 < q := by linarith only [hq]
  have hR : 0 < finitePAdaptiveRate (1/q) := finitePAdaptiveRate_pos (1/q) (by positivity)
  have hH : 0 < H := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hform' : 1 < U/Z+V*Z := by
    change 1 < 2400*H*C^3/Z+finitePAdaptiveRate (1/q)*T^2*Z/(A^3*C^5) at hform
    convert hform using 1 <;> dsimp [U,V] <;> ring
  have heqlo : 4*U^2/(C*(1-1/4000 : ℝ)) =
      4*(2400 : ℝ)^2*H^2*C^5/(1-1/4000 : ℝ) := by
    dsimp [U]
    field_simp [hC.ne']
    <;> ring
  have heqhi : 1/(4*V^2*C*(1+1/4000 : ℝ)) =
      A^6*C^9/(4*(finitePAdaptiveRate (1/q))^2*T^4*(1+1/4000 : ℝ)) := by
    dsimp [V]
    field_simp [hA.ne',hB.ne',hT.ne',hC.ne',hR.ne']
    <;> ring
  apply finite_closed_window_incompatible C D Z U V (1/4000) hC hZ hU hV
    (by norm_num) (by norm_num) hlo hhi hform'
  · rw [heqlo]
    exact hleft
  · rw [heqhi]
    exact hright

end D1Bound5
end
