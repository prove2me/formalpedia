-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.two_small_bounded_fourth_fifth_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:07:28.055319+00:00
-- url     : https://prove2.me/submissions/b3fb92df-9b20-49ad-8eba-c7944b17a773

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
import Theorems.Thm_D1Bound5_IsD1Tuple_direct_four_integer_inequality
import Theorems.Thm_D1Bound5_IsD1Tuple_four_anchor_V_window
import Theorems.Thm_D1Bound5_IsD1Tuple_two_small_growth_inputs
import Theorems.Thm_D1Bound5_IsD1Tuple_two_small_ordinary_at
import Theorems.Thm_D1Bound5_full_ring_finiteM_closed_interval_excluded
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_two_small_M_window_brackets
import Theorems.Thm_D1Bound5_two_small_M_window_contains
import Theorems.Thm_D1Bound5_two_small_large_C_V_parameters
import Theorems.Thm_D1Bound5_two_small_large_C_direct_four_parameters
import Theorems.Thm_D1Bound5_two_small_large_C_seventh_power

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- The remaining two-small box: when the third and fourth entries
are below10^8, V nonvanishing forces direct-four nonvanishing, whose
seventh-power lower bound falls inside the actual M forbidden window. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hB3 : ‖phi (a 1 : K)‖ < 3) (hS3 : 3 ≤ ‖phi (a 2 : K)‖)
    (hT8 : ‖phi (a 3 : K)‖ < (10 : ℝ)^8) :
    ‖phi (a 4 : K)‖ < (10 : ℝ)^100 := by
  classical
  by_contra hbad
  have hCbig := le_of_not_gt hbad
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let A := ‖f (a 0)‖
  let B := ‖f (a 1)‖
  let S := ‖f (a 2)‖
  let T := ‖f (a 3)‖
  let C := ‖f (a 4)‖
  let D := ‖f (a 5)‖
  change B < 3 at hB3
  change 3 ≤ S at hS3
  change T < (10 : ℝ)^8 at hT8
  change (10 : ℝ)^100 ≤ C at hCbig
  have hA : 1 ≤ A := one_le_norm_integer hK phi (ha.2.1 0)
  have hB : 1 ≤ B := one_le_norm_integer hK phi (ha.2.1 1)
  have hB0 : 0 < B := by linarith only [hB]
  have hS0 : 0 < S := by linarith only [hS3]
  have hST : S ≤ T := hmon (by decide : (2 : Fin 6) ≤ 3)
  have hS8 : S < (10 : ℝ)^8 := hST.trans_lt hT8
  have hT0 : 0 < T := hS0.trans_le hST
  have hC0 : 0 < C := hT0.trans_le (hmon (by decide : (3 : Fin 6) ≤ 4))
  have hD0 : 0 < D := hC0.trans_le (hmon (by decide : (4 : Fin 6) ≤ 5))
  have hg := ha.two_small_growth_inputs hK phi a hmon hS3
  have hp := two_small_large_C_V_parameters A B S T C D hA hB hB3 hS3 hST hS8 hT8 hCbig hg.2.1
  have hw := ha.four_anchor_V_window hK phi a hmon hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
  have hV : (2/5 : ℝ)*A^2*C^5/T^2 < D := by
    rcases hw with hw | hw
    · exact False.elim (lt_asymm hw hp.2.2.2.2)
    · exact hw
  have hfour := two_small_large_C_direct_four_parameters A B S T C D hA
    (hmon (by decide : (0 : Fin 6) ≤ 1)) hB0 hB3 hS0 hT0 hS8 hT8 hCbig hV
  obtain ⟨Z,hZ,hCZ,hroot,hform⟩ :=
    ha.direct_four_integer_inequality hK phi a hmon hp.1 hfour.1 hfour.2
  have hseven := two_small_large_C_seventh_power A B S T C D Z hA hB0 hB3 hS0 hT0
    hS8 hT8 hCbig hZ hCZ hroot hform
  have hC8 : (10 : ℝ)^8 ≤ C := by norm_num at hCbig ⊢; linarith only [hCbig]
  have hheight := ha.two_small_ordinary_at hK phi a hmon hB3 4 (by decide) (by decide) hC8
  have hbracket := two_small_M_window_brackets C D hCbig hseven hheight hD0
  have hcontains := two_small_M_window_contains A B S C hA hB0 hB3 hS0 hS8 hC0
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
  let b : Fin 3 → 𝓞 K := fun i => a (![0,1,2] i)
  have hb : Function.Injective b :=
    ha.1.comp (by decide : Function.Injective (![0,1,2] : Fin 3 → Fin 6))
  have hbmon : Monotone (fun i => ‖phi (b i : K)‖) := by
    have hi : Monotone (![0,1,2] : Fin 3 → Fin 6) := by decide
    exact fun i j hij => hmon (hi hij)
  have hAC : 1000 ≤ A*C := by
    have hh := mul_le_mul_of_nonneg_right hA hC0.le
    nlinarith only [hh,hp.1]
  exact full_ring_finiteM_closed_interval_excluded hK phi hTup b (a 4) (a 5)
    (fun i => hmem _) (hmem 4) (hmem 5) hb
    (by intro i; exact ha.1.ne (by fin_cases i <;> decide))
    (by intro i; exact ha.1.ne (by fin_cases i <;> decide))
    (ha.1.ne (by decide)) hbmon (by change 4*S ≤ C; linarith only [hp.2.1,hST])
    (hmon (by decide : (4 : Fin 6) ≤ 5)) hAC
    (hcontains.1.trans hbracket.1) (hbracket.2.trans hcontains.2)



end D1Bound5
end
