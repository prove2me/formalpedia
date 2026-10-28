-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.three_anchor_general_detailed_alternative
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:51:52.578986+00:00
-- url     : https://prove2.me/submissions/2024e20d-ebe6-4c92-af57-ede78eb46777

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
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_coherent_cpow_half_sq
import Theorems.Thm_D1Bound5_coherent_three_separated_bounds
import Theorems.Thm_D1Bound5_coherent_three_zero_bootstrap
import Theorems.Thm_D1Bound5_full_ring_three_general_window
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- The actual three-anchor alternative. A zero form first creates its
own terminal separation, so the quadratic lower branch has no assumed
separation or hidden nonvanishing premise. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hP : 1000 ≤ ‖phi (a 3 : K)‖)
    (hSP : 4*‖phi (a 2 : K)‖ ≤ ‖phi (a 3 : K)‖) :
    (5*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖^2 <
        ‖phi (a 4 : K)‖ ∧
      ‖phi (a 4 : K)‖ < 15*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖^2) ∨
    ‖phi (a 4 : K)‖ < 101*‖phi (a 1 : K)‖^2*‖phi (a 2 : K)‖^4/‖phi (a 3 : K)‖ ∨
    ‖phi (a 0 : K)‖^2*‖phi (a 3 : K)‖^5/(37*‖phi (a 2 : K)‖^2) < ‖phi (a 4 : K)‖ := by
  classical
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let b : Fin 3 → 𝓞 K := fun i => a (![0,1,2] i)
  let v : Fin 3 → ℂ := fun i => f (b i)
  let A := ‖f (a 0)‖
  let B := ‖f (a 1)‖
  let S := ‖f (a 2)‖
  let P := ‖f (a 3)‖
  let Q := ‖f (a 4)‖
  change 1000 ≤ P at hP
  change 4*S ≤ P at hSP
  let eta : ℂ := (f (a 3)*f (a 4))^(1/2 : ℂ)
  have heta : eta^2 = f (a 3)*f (a 4) := coherent_cpow_half_sq _
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hb : Function.Injective b :=
    ha.1.comp (by decide : Function.Injective (![0,1,2] : Fin 3 → Fin 5))
  have hv : Function.Injective v := hf.comp hb
  have hn (i : Fin 5) : 1 ≤ ‖f (a i)‖ := one_le_norm_integer hK phi (ha.2.1 i)
  have hA : 1 ≤ A := hn 0
  have hB : 1 ≤ B := hn 1
  have hS : 1 ≤ S := hn 2
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hB]
  have hS0 : 0 < S := by linarith only [hS]
  have hP0 : 0 < P := by linarith only [hP]
  have hQ : P ≤ Q := hmon (by decide)
  have hAP : 1000 ≤ A*P := by
    have hh := mul_le_mul_of_nonneg_right hA hP0.le
    nlinarith only [hh,hP]
  have hPQ : 10000 < P*Q := by
    have hh := mul_le_mul_of_nonneg_left hQ hP0.le
    nlinarith only [hP,hh,sq_nonneg (P-1000)]
  have hva : ∀ i, A ≤ ‖v i‖ := by
    intro i
    apply hmon
    exact Fin.zero_le _
  have hprod : (∏ i, ‖v i‖) = A*B*S := by
    simp [v,b,A,B,S,Fin.prod_univ_succ,mul_assoc]
  by_cases hL : coherentQuotientForm v (coherentVandermonde3 v)
      (f (a 3)) (f (a 4)) eta = 0
  · left
    have hboot := coherent_three_zero_bootstrap v hv (f (a 3)) (f (a 4)) eta A
      hA0 hva hP0 hQ (by linarith only [hAP]) hPQ heta hL
    rw [hprod] at hboot
    change A*B*S*P^2 < Q at hboot
    have hAB1 : 1 ≤ A*B := by
      have hh := mul_le_mul hA hB (by norm_num : (0 : ℝ) ≤ 1) hA0.le
      simpa only [one_mul] using hh
    have hV : 1 ≤ A*B*S := by
      have hh := mul_le_mul hAB1 hS (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ A*B)
      simpa only [one_mul] using hh
    have hsep : 4*P ≤ Q := by
      have hh := mul_le_mul_of_nonneg_right hV (sq_nonneg P)
      nlinarith only [hh,hboot,hP,sq_nonneg (P-1000)]
    have hforms := coherent_three_separated_bounds v (f (a 3)) (f (a 4)) eta hv hA0
      (hmon (by decide : (0 : Fin 5) ≤ 1)) (hmon (by decide : (1 : Fin 5) ≤ 2))
      hP0 hAP hsep hPQ heta
    exact hforms.2 hL
  · right
    let Tup : Finset (𝓞 K) := Finset.univ.image a
    have hmem (i : Fin 5) : a i ∈ Tup := Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
    have hTup : IsD1 Tup := by
      constructor
      · intro x hx
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
        exact ha.2.1 i
      · intro x hx y hy hxy
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
        exact ha.2.2 i j (fun hij => hxy (congrArg a hij))
    exact full_ring_three_general_window hK phi hTup (hmem 3) (hmem 4)
      (ha.1.ne (by decide)) b hb (fun i => hmem _)
      (by intro i; exact ha.1.ne (by fin_cases i <;> decide))
      (by intro i; exact ha.1.ne (by fin_cases i <;> decide))
      (hmon (by decide : (0 : Fin 5) ≤ 1)) (hmon (by decide : (1 : Fin 5) ≤ 2))
      hSP (by change 9 ≤ A*P; linarith only [hAP]) hQ
      (by change 4000 ≤ P*Q; linarith only [hPQ]) eta heta hL

end D1Bound5
end
