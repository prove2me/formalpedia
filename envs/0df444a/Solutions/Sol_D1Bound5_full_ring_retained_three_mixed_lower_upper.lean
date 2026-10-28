-- Prove2me | solution 1 for D1Bound5.full_ring_retained_three_mixed_lower_upper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:38:57.194663+00:00
-- url     : https://prove2.me/submissions/1cf5f2b7-27d8-439d-bad7-6b15f4a5a423

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
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_CoherentRetainedMixedForms_Definitions
import Definitions.Def_D1Bound5_CoherentThreeParameters_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_CoherentRetainedRow_parameters
import Theorems.Thm_D1Bound5_coherent_retained_mixed_size_parameters
import Theorems.Thm_D1Bound5_coherent_three_parameter_form_bounds
import Theorems.Thm_D1Bound5_full_ring_coherent_three_one_le_norm
import Theorems.Thm_D1Bound5_full_ring_coherent_two_strong_gap
import Theorems.Thm_D1Bound5_full_ring_coherent_two_strong_gap_main

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5





/-- Both manuscript parameter rows for the actual retained three-anchor
form with a potentially small first entry. The two successive actual
L2 gaps supply the zero-window contradiction and the integral lower
bound; no root integrality or nonvanishing premise is assumed. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {Tup : Finset (𝓞 K)} (hTup : IsD1 Tup)
    (a : Fin 5 → 𝓞 K) (hinj : Function.Injective a) (hmem : ∀ i, a i ∈ Tup)
    (hA : 1 ≤ ‖phi (a 0 : K)‖) (hB : 3 ≤ ‖phi (a 1 : K)‖)
    (hAB : ‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖)
    (hBS : ‖phi (a 1 : K)‖ ≤ ‖phi (a 2 : K)‖)
    (hfrontier : 2*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖)
    (hproduct : 3*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖ < ‖phi (a 4 : K)‖)
    (H lam U : ℝ) (hrow : CoherentRetainedRow H lam U)
    (hAT : H ≤ ‖phi (a 0 : K)‖*‖phi (a 3 : K)‖)
    (eta : ℂ) (heta : eta^2 = phi (a 3 : K)*phi (a 4 : K)) :
    let v : Fin 3 → ℂ := fun i => phi (a (![0,1,2] i) : K)
    let L := coherentQuotientForm v (coherentVandermonde3 v)
      (phi (a 3 : K)) (phi (a 4 : K)) eta
    let Z := ‖coherentTerminalRoot (phi (a 3 : K)) (phi (a 4 : K)) eta‖
    ‖phi (a 1 : K)‖^2*‖phi (a 3 : K)‖^3 < (10001/10000 : ℝ)*‖phi (a 4 : K)‖ ∧
      L ≠ 0 ∧ 1 ≤ ‖L‖ ∧
      ‖L‖ < 51*‖coherentVandermonde3 v‖/(100*Z) +
        lam*‖coherentVandermonde3 v‖*Z/
          (‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖^3) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let b : Fin 3 → 𝓞 K := fun i => a (![0,1,2] i)
  let v : Fin 3 → ℂ := fun i => f (b i)
  let A := ‖f (a 0)‖
  let B := ‖f (a 1)‖
  let S := ‖f (a 2)‖
  let P := ‖f (a 3)‖
  let Q := ‖f (a 4)‖
  have hA0 : 0 < A := by change 0 < ‖phi (a 0 : K)‖; linarith only [hA]
  have hS3 : 3 ≤ S := hB.trans hBS
  have hB0 : 0 < B := by change 0 < ‖phi (a 1 : K)‖; linarith only [hB]
  have hS0 : 0 < S := by linarith only [hS3]
  have hP0 : 0 < P := lt_trans (by positivity : 0 < 2*A*B*S) hfrontier
  have hH32 : 32 ≤ H := by
    rcases hrow with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
  have hparams := coherent_retained_mixed_size_parameters A B S P Q
    hA hB hBS (hH32.trans hAT) hfrontier hproduct
  have hBS' : B ≤ S := hBS
  have h5B : 5*B ≤ P := by linarith only [hBS',hparams.1]
  have hAP32 : 32 ≤ A*P := by linarith only [hparams.2.2.1]
  have hfirst := full_ring_coherent_two_strong_gap hK phi hTup
    (hmem 0) (hmem 1) (hmem 3) (hmem 4)
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
    eta heta hAB hB h5B hAP32
    hparams.2.1 hparams.2.2.2.2.1
  have hsecond := full_ring_coherent_two_strong_gap_main hK phi hTup
    (hmem 1) (hmem 2) (hmem 3) (hmem 4)
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
    hBS hS3 hparams.1 (hparams.2.2.2.2.2.1 hfirst) (Or.inl hB)
  have hlarge := hparams.2.2.2.2.2.2 hsecond
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hb : Function.Injective b :=
    hinj.comp (by decide : Function.Injective (![0,1,2] : Fin 3 → Fin 5))
  have hv : Function.Injective v := hf.comp hb
  have hva : ∀ i, A ≤ ‖v i‖ := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact hAB
    · exact hAB.trans hBS
  obtain ⟨hH,hH48,hU,hell,hu,hlam,hwlo,hwhi⟩ := hrow.parameters
  have hforms := coherent_three_parameter_form_bounds v hv (f (a 3)) (f (a 4)) eta
    A H lam U hA0 hva hP0 hparams.2.2.2.1 hparams.2.2.2.2.1
    hH hAT heta hell hu hlam hwlo hwhi
  have hprod : (∏ i, ‖v i‖) = A*B*S := by
    simp [v,b,A,B,S,Fin.prod_univ_succ,mul_assoc]
  rw [hprod] at hforms
  have hnonzero : coherentQuotientForm v (coherentVandermonde3 v)
      (f (a 3)) (f (a 4)) eta ≠ 0 := by
    intro hz
    have hupper := (hforms.2 hz).2
    have hbound := mul_le_mul_of_nonneg_right hU
      (by positivity : 0 ≤ A*B*S*P^2)
    nlinarith only [hupper,hlarge,hbound]
  have hbm : ∀ i, b i ∈ Tup := fun i => hmem _
  have hbp : ∀ i, b i ≠ a 3 := by
    intro i
    exact hinj.ne (by fin_cases i <;> decide)
  have hbq : ∀ i, b i ≠ a 4 := by
    intro i
    exact hinj.ne (by fin_cases i <;> decide)
  have hdelta : phi ((coherentVandermonde3 b : 𝓞 K) : K) = coherentVandermonde3 v := by
    change f (coherentVandermonde3 b) = coherentVandermonde3 v
    simp [coherentVandermonde3,v]
  have hnonzero' : coherentQuotientForm (fun i => phi (b i : K))
      (phi ((coherentVandermonde3 b : 𝓞 K) : K)) (phi (a 3 : K)) (phi (a 4 : K)) eta ≠ 0 := by
    rw [hdelta]
    exact hnonzero
  have hlow := full_ring_coherent_three_one_le_norm hK phi hTup
    (hmem 3) (hmem 4) (hinj.ne (by decide)) b hb hbm hbp hbq eta heta hnonzero'
  rw [hdelta] at hlow
  exact ⟨hsecond,hnonzero,hlow,hforms.1⟩

end D1Bound5
end
