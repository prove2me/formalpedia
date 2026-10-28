-- Prove2me | solution 1 for D1Bound5.full_ring_all_large_retained_monomial
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:18:08.65591+00:00
-- url     : https://prove2.me/submissions/6202b615-8c0b-4e63-a4de-62cfba6a5e79

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_all_large_retained_gap_monomial
import Theorems.Thm_D1Bound5_coherent_three_vandermonde_ratio_bounds
import Theorems.Thm_D1Bound5_full_ring_retained_three_h48_gap

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5



/-- With the sharpened four-entry frontier, the retained actual tuple
gap gives the coefficient 400 used in the no-small-entry overlap table. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {Tup : Finset (𝓞 K)} (hTup : IsD1 Tup)
    (a : Fin 5 → 𝓞 K) (hinj : Function.Injective a) (hmem : ∀ i, a i ∈ Tup)
    (hA : 3 ≤ ‖phi (a 0 : K)‖)
    (hAB : ‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖)
    (hBS : ‖phi (a 1 : K)‖ ≤ ‖phi (a 2 : K)‖)
    (hfrontier : 3*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖)
    (hproduct : 3*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖ < ‖phi (a 4 : K)‖) :
    400*(‖phi (a 0 : K)‖^7*‖phi (a 1 : K)‖^5*‖phi (a 2 : K)‖^3) < ‖phi (a 4 : K)‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let v : Fin 3 → ℂ := fun i => f (a (![0,1,2] i))
  let A := ‖f (a 0)‖
  let B := ‖f (a 1)‖
  let S := ‖f (a 2)‖
  let P := ‖f (a 3)‖
  let C := ‖f (a 4)‖
  let R := ‖coherentVandermonde3 v‖/(B*S^2)
  have hA0 : 0 < A := by change 0<‖phi (a 0 : K)‖; linarith only [hA]
  have hB3 : 3 ≤ B := hA.trans hAB
  have hB0 : 0 < B := by linarith
  have hS0 : 0 < S := hB0.trans_le hBS
  have hprod0 : 0 < A*B*S := by positivity
  change 3*A*B*S < P at hfrontier
  have hfront2 : 2*A*B*S < P := by nlinarith only [hfrontier,hprod0]
  have hret := full_ring_retained_three_h48_gap hK phi hTup a hinj hmem
    hA hAB hBS hfront2 hproduct
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hv : Function.Injective v :=
    hf.comp (hinj.comp (by decide : Function.Injective (![0,1,2] : Fin 3 → Fin 5)))
  have hratio := coherent_three_vandermonde_ratio_bounds v hv hA0 hAB hBS
  have hp5 : (3*A*B*S)^5 ≤ P^5 := by gcongr
  have hbase : 3^5*(A^7*B^5*S^3) ≤ A^2*P^5/S^2 := by
    calc
      _ = A^2*(3*A*B*S)^5/S^2 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp5 (sq_nonneg A)) (sq_nonneg S)
  have hmon : 3^5*((9999/10000 : ℝ)*(200/19)^2)*
      (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2*(A^7*B^5*S^3) < C := by
    have h := mul_le_mul_of_nonneg_left hbase
      (by positivity : 0 ≤ ((9999/10000 : ℝ)*(200/19)^2)*
        (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2)
    have hc : ((9999/10000 : ℝ)*(200/19)^2)*
        (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2*(A^2*P^5/S^2) < C := hret
    nlinarith only [h,hc]
  exact all_large_retained_gap_monomial A B S C R hA hB3 hS0 hratio.1 hratio.2 hmon

end D1Bound5
end
