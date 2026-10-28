-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.three_small_not_fixed_and_two_large
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:54:02.013377+00:00
-- url     : https://prove2.me/submissions/c8f1b09c-1b8e-4073-b9db-b693418c31bf

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
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Definitions.Def_D1Bound5_TwoSmallHeightScalar_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_four_anchor_V_window
import Theorems.Thm_D1Bound5_IsD1Tuple_three_small_pair_at
import Theorems.Thm_D1Bound5_IsD1Tuple_two_small_ordinary_at
import Theorems.Thm_D1Bound5_full_ring_finiteM_closed_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteQ_closed_interval_excluded
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_ordinary_height_power_upper
import Theorems.Thm_D1Bound5_three_small_fixed_M_window_contains
import Theorems.Thm_D1Bound5_three_small_fixed_Q_window_contains
import Theorems.Thm_D1Bound5_three_small_fixed_V_growth
import Theorems.Thm_D1Bound5_three_small_fixed_V_parameters
import Theorems.Thm_D1Bound5_three_small_fixed_upper_and_overlap
import Theorems.Thm_D1Bound5_three_small_pair_growth

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- A fixed fourth extension below85 cannot coexist with two extensions
above10^40. The actual V form starts the lower bound, and the actual Q
and M closed windows overlap all the way to the ordinary upper bound. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hS3 : ‖phi (a 2 : K)‖ < 3) (hT85 : ‖phi (a 3 : K)‖ < 85)
    (hCbig : (10 : ℝ)^40 ≤ ‖phi (a 4 : K)‖) : False := by
  classical
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let A := ‖f (a 0)‖
  let B := ‖f (a 1)‖
  let S := ‖f (a 2)‖
  let T := ‖f (a 3)‖
  let C := ‖f (a 4)‖
  let D := ‖f (a 5)‖
  change S < 3 at hS3
  change T < 85 at hT85
  change (10 : ℝ)^40 ≤ C at hCbig
  have hn (i : Fin 6) : 1 ≤ ‖f (a i)‖ := one_le_norm_integer hK phi (ha.2.1 i)
  have hA : 1 ≤ A := hn 0
  have hB : 0 < B := by have hh := hn 1; linarith only [hh]
  have hS : 0 < S := by have hh := hn 2; linarith only [hh]
  have hT : 0 < T := by have hh := hn 3; linarith only [hh]
  have hC : 0 < C := by have hh := hn 4; linarith only [hh]
  have hD : 0 < D := by have hh := hn 5; linarith only [hh]
  have hB3 : B < 3 := (hmon (by decide : (1 : Fin 6) ≤ 2)).trans_lt hS3
  have hC1000 : 1000 ≤ C := by norm_num at hCbig; linarith only [hCbig]
  have halt := ha.three_small_pair_at hK phi a hmon hS3 4 5 (by decide) (by decide) hC1000
  have hDgrow : 5*C^2 < D := three_small_pair_growth C D hC1000 halt
  have hp := three_small_fixed_V_parameters A B S T C D hA hB hB3 hS hS3 hT hT85 hCbig hDgrow
  have hw := ha.four_anchor_V_window hK phi a hmon hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
  have hV : (2/5 : ℝ)*A^2*C^5/T^2 < D := by
    rcases hw with hw | hw
    · exact False.elim (lt_asymm hw hp.2.2.2.2)
    · exact hw
  have hDlo := three_small_fixed_V_growth A T C D hA hT hT85 hCbig hV
  have hC8 : (10 : ℝ)^8 ≤ C := by norm_num at hCbig ⊢; linarith only [hCbig]
  have hheight := ha.two_small_ordinary_at hK phi a hmon hB3 4 (by decide) (by decide) hC8
  have hupper := ordinary_height_power_upper C D hCbig hD hheight
  have hbracket := three_small_fixed_upper_and_overlap C D hCbig hupper
  have hQcontains := three_small_fixed_Q_window_contains C hC
  have hMcontains := three_small_fixed_M_window_contains A B S C hA hB hB3 hS hS3 hC
  let Tup : Finset (𝓞 K) := Finset.univ.image a
  have hmem (i : Fin 6) : a i ∈ Tup := Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have hTup : IsD1 Tup := by
    constructor
    · intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact ha.2.1 i
    · intro x hx y hy hxy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
      exact ha.2.2 i j (fun hij => hxy (congrArg a hij))
  let b : Fin 4 → 𝓞 K := fun i => a (![0,1,2,3] i)
  have hb : Function.Injective b :=
    ha.1.comp (by decide : Function.Injective (![0,1,2,3] : Fin 4 → Fin 6))
  have hC340 : 4*(85 : ℝ) ≤ C := by norm_num at hCbig; linarith only [hCbig]
  by_cases hQupper : D ≤ C^7/(10 : ℝ)^29
  · apply full_ring_finiteQ_closed_interval_excluded hK phi hTup b (a 4) (a 5)
      (fun i => hmem _) (hmem 4) (hmem 5) hb
      (by intro i; exact ha.1.ne (by fin_cases i <;> decide))
      (by intro i; exact ha.1.ne (by fin_cases i <;> decide))
      (ha.1.ne (by decide)) 1 85 (by norm_num)
      (fun i => hn _) (by
        intro i
        have hh : ‖phi (b i : K)‖ ≤ T := hmon (by fin_cases i <;> decide)
        exact hh.trans hT85.le)
      hC340 (hmon (by decide : (4 : Fin 6) ≤ 5)) (by change 1000 ≤ (1 : ℝ)*C; simpa only [one_mul] using hC1000)
    · exact hQcontains.1.trans hDlo.le
    · change D ≤ (1 : ℝ)^4*C^7/(9*(85 : ℝ)^2*(1+1/4000))
      simpa only [one_pow,one_mul] using hQupper.trans hQcontains.2
  · let c : Fin 3 → 𝓞 K := fun i => a (![0,1,2] i)
    have hc : Function.Injective c :=
      ha.1.comp (by decide : Function.Injective (![0,1,2] : Fin 3 → Fin 6))
    have hcmon : Monotone (fun i => ‖phi (c i : K)‖) := by
      have hi : Monotone (![0,1,2] : Fin 3 → Fin 6) := by decide
      exact fun i j hij => hmon (hi hij)
    have hAC : 1000 ≤ A*C := by
      have hh := mul_le_mul_of_nonneg_right hA hC.le
      nlinarith only [hh,hC1000]
    exact full_ring_finiteM_closed_interval_excluded hK phi hTup c (a 4) (a 5)
      (fun i => hmem _) (hmem 4) (hmem 5) hc
      (by intro i; exact ha.1.ne (by fin_cases i <;> decide))
      (by intro i; exact ha.1.ne (by fin_cases i <;> decide))
      (ha.1.ne (by decide)) hcmon (by change 4*S ≤ C; linarith only [hS3,hC1000])
      (hmon (by decide : (4 : Fin 6) ≤ 5)) hAC
      (hMcontains.1.trans (hbracket.2.trans (le_of_lt (lt_of_not_ge hQupper))))
      (hbracket.1.le.trans hMcontains.2)

end D1Bound5
end
