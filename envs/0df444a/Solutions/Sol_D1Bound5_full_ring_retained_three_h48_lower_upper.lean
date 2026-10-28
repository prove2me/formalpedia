-- Prove2me | solution 1 for D1Bound5.full_ring_retained_three_h48_lower_upper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:53:10.093121+00:00
-- url     : https://prove2.me/submissions/2541a80d-07f3-4fc7-ae7f-0fe48eaa8539

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
import Definitions.Def_D1Bound5_CoherentThreeParameters_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_coherent_retained_h48_size_parameters
import Theorems.Thm_D1Bound5_coherent_three_parameter_form_bounds
import Theorems.Thm_D1Bound5_coherent_three_parameter_rows
import Theorems.Thm_D1Bound5_full_ring_coherent_three_one_le_norm
import Theorems.Thm_D1Bound5_full_ring_coherent_two_strong_gap_main

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5



/-- The actual retained three-anchor form has both its integral lower
bound and the H48 analytic upper bound in the no-small-entry branch.
The nonzero-form premise is discharged using the actual strong L2 gap;
no chosen-root integrality or tail estimate is assumed. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {Tup : Finset (𝓞 K)} (hTup : IsD1 Tup)
    (a : Fin 5 → 𝓞 K) (hinj : Function.Injective a) (hmem : ∀ i, a i ∈ Tup)
    (hA : 3 ≤ ‖phi (a 0 : K)‖)
    (hAB : ‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖)
    (hBS : ‖phi (a 1 : K)‖ ≤ ‖phi (a 2 : K)‖)
    (hfrontier : 2*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖)
    (hproduct : 3*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖ < ‖phi (a 4 : K)‖)
    (eta : ℂ) (heta : eta^2 = phi (a 3 : K)*phi (a 4 : K)) :
    let v : Fin 3 → ℂ := fun i => phi (a (![0,1,2] i) : K)
    let L := coherentQuotientForm v (coherentVandermonde3 v)
      (phi (a 3 : K)) (phi (a 4 : K)) eta
    let Z := ‖coherentTerminalRoot (phi (a 3 : K)) (phi (a 4 : K)) eta‖
    L ≠ 0 ∧ 1 ≤ ‖L‖ ∧
      ‖L‖ < 51*‖coherentVandermonde3 v‖/(100*Z) +
        (19/200 : ℝ)*‖coherentVandermonde3 v‖*Z/
          (‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖^3) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let b : Fin 3 → 𝓞 K := fun i => a (![0,1,2] i)
  let v : Fin 3 → ℂ := fun i => f (b i)
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hb : Function.Injective b :=
    hinj.comp (by decide : Function.Injective (![0,1,2] : Fin 3 → Fin 5))
  have hv : Function.Injective v := hf.comp hb
  let A := ‖f (a 0)‖
  let B := ‖f (a 1)‖
  let S := ‖f (a 2)‖
  let P := ‖f (a 3)‖
  let Q := ‖f (a 4)‖
  have hA0 : 0 < A := by change 0<‖phi (a 0 : K)‖; linarith only [hA]
  have hB3 : 3 ≤ B := hA.trans hAB
  have hS3 : 3 ≤ S := hB3.trans hBS
  have hparams := coherent_retained_h48_size_parameters A B S P Q hA hAB hBS hfrontier hproduct
  have hP0 : 0 < P := by nlinarith only [hparams.1,hS3]
  have hgap := full_ring_coherent_two_strong_gap_main hK phi hTup
    (hmem 1) (hmem 2) (hmem 3) (hmem 4)
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
    hBS hS3 hparams.1 hparams.2.1 (Or.inl hB3)
  have hlarge : 15*A*B*S*P^2 < Q := hparams.2.2.2.2.2 hgap
  have hva : ∀ i, A ≤ ‖v i‖ := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact hAB
    · exact hAB.trans hBS
  have hrows := coherent_three_parameter_rows.2
  have hforms := coherent_three_parameter_form_bounds v hv (f (a 3)) (f (a 4)) eta
    A 48 (19/200) 15 hA0 hva hP0 hparams.2.2.2.1 hparams.2.2.2.2.1
    (by norm_num) hparams.2.2.1 heta hrows.1
    (by norm_num [coherentThreeUpperConstant,coherentThreeTailConstant])
    hrows.2.1 hrows.2.2.1 hrows.2.2.2
  have hprod : (∏ i, ‖v i‖) = A*B*S := by
    simp [v,b,A,B,S,Fin.prod_univ_succ,mul_assoc]
  rw [hprod] at hforms
  have hnonzero : coherentQuotientForm v (coherentVandermonde3 v)
      (f (a 3)) (f (a 4)) eta ≠ 0 := by
    intro hz
    have hupper := (hforms.2 hz).2
    nlinarith only [hupper,hlarge]
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
  exact ⟨hnonzero,hlow,hforms.1⟩

end D1Bound5
end
