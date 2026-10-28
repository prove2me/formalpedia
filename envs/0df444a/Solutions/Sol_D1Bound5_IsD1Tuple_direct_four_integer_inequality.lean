-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.direct_four_integer_inequality
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:36:14.054244+00:00
-- url     : https://prove2.me/submissions/0d547362-9e12-436f-be60-6ceb175fcf4b

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
import Mathlib.Tactic.Positivity
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coherent_analytic_terminal_root_sq
import Theorems.Thm_D1Bound5_coherent_cpow_half_sq
import Theorems.Thm_D1Bound5_coherent_direct_four
import Theorems.Thm_D1Bound5_finite_tuple_root_relative_norm
import Theorems.Thm_D1Bound5_full_ring_coherent_four_one_le_norm
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

private theorem directFour_product_size (P Q : ℝ)
    (hP : 1000 ≤ P) (hQ : 1000*P ≤ Q) :
    0 < P ∧ 0 < Q ∧ 4000 ≤ P*Q := by
  have hp : 0 < P := (by norm_num : (0 : ℝ) < 1000).trans_le hP
  have hq : 0 < Q := (mul_pos (by norm_num : (0 : ℝ) < 1000) hp).trans_le hQ
  have hh := mul_le_mul_of_nonneg_left hQ hp.le
  exact ⟨hp,hq,by nlinarith only [hP,hh,sq_nonneg (P-1000)]⟩

private theorem directFour_terminal_size (P Q Z : ℝ)
    (hP : 0 < P) (hQ : 1000*P ≤ Q) (hZ : 0 ≤ Z)
    (hlo : (1-1/4000 : ℝ)*P*Q ≤ Z^2)
    (hhi : Z^2 ≤ (1+1/4000 : ℝ)*P*Q) :
    0 < Z ∧ P/2 < Z ∧ Z^2 ≤ 2*P*Q := by
  have hq : 0 < Q := (mul_pos (by norm_num : (0 : ℝ) < 1000) hP).trans_le hQ
  have hscale := mul_le_mul_of_nonneg_left hQ hP.le
  have hhalf : P/2 < Z := by
    by_contra hbad
    have hh : Z ≤ P/2 := le_of_not_gt hbad
    have hsq : Z^2 ≤ (P/2)^2 := by gcongr
    nlinarith only [hscale,hlo,hsq,sq_pos_of_pos hP]
  refine ⟨by linarith only [hhalf,hP],hhalf,?_⟩
  nlinarith only [hhi,mul_nonneg hP.le hq.le]

/-- Beyond the proved zero-form upper window, an actual sextuple
supplies the direct-four integral inequality and terminal norm bounds. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hC : 1000 ≤ ‖phi (a 4 : K)‖)
    (hD : 1000*‖phi (a 4 : K)‖ ≤ ‖phi (a 5 : K)‖)
    (hzeroExcluded : 17*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*
      ‖phi (a 3 : K)‖*‖phi (a 4 : K)‖^3 ≤ ‖phi (a 5 : K)‖) :
    ∃ Z : ℝ, 0 < Z ∧ ‖phi (a 4 : K)‖/2 < Z ∧
      Z^2 ≤ 2*‖phi (a 4 : K)‖*‖phi (a 5 : K)‖ ∧
      1 < 13*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖^2*‖phi (a 3 : K)‖^3/Z+
        49*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖^2*Z/
          (50*‖phi (a 0 : K)‖*‖phi (a 4 : K)‖^4) := by
  classical
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let b : Fin 4 → 𝓞 K := fun i => a (![0,1,2,3] i)
  let v : Fin 4 → ℂ := fun i => f (b i)
  let p := f (a 4)
  let q := f (a 5)
  change 1000 ≤ ‖p‖ at hC
  change 1000*‖p‖ ≤ ‖q‖ at hD
  change 17*‖v 0‖*‖v 1‖*‖v 2‖*‖v 3‖*‖p‖^3 ≤ ‖q‖ at hzeroExcluded
  let eta : ℂ := (p*q)^(1/2 : ℂ)
  have heta : eta^2 = p*q := coherent_cpow_half_sq _
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hb : Function.Injective b :=
    ha.1.comp (by decide : Function.Injective (![0,1,2,3] : Fin 4 → Fin 6))
  have hA : 1 ≤ ‖f (a 0)‖ := one_le_norm_integer hK phi (ha.2.1 0)
  have hforms := coherent_direct_four v (hf.comp hb) p q eta hA
    (hmon (by decide : (0 : Fin 6) ≤ 1)) (hmon (by decide : (1 : Fin 6) ≤ 2))
    (hmon (by decide : (2 : Fin 6) ≤ 3)) (hmon (by decide : (3 : Fin 6) ≤ 4)) hC hD heta
  have hL : coherentQuotientForm v (coherentVandermonde4 v) p q eta ≠ 0 := by
    intro hz
    exact not_lt_of_ge hzeroExcluded (hforms.2 hz).2
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
  have hdelta : phi ((coherentVandermonde4 b : 𝓞 K) : K) = coherentVandermonde4 v := by
    change f (coherentVandermonde4 b) = coherentVandermonde4 v
    simp [coherentVandermonde4,v]
  have hL' : coherentQuotientForm (fun i => phi (b i : K))
      (phi ((coherentVandermonde4 b : 𝓞 K) : K)) (phi (a 4 : K)) (phi (a 5 : K)) eta ≠ 0 := by
    rw [hdelta]
    exact hL
  have hlow := full_ring_coherent_four_one_le_norm hK phi hTup (hmem 4) (hmem 5)
    (ha.1.ne (by decide)) b hb (fun i => hmem _)
    (by intro i; exact ha.1.ne (by fin_cases i <;> decide))
    (by intro i; exact ha.1.ne (by fin_cases i <;> decide)) eta heta hL'
  rw [hdelta] at hlow
  change 1 ≤ ‖coherentQuotientForm v (coherentVandermonde4 v) p q eta‖ at hlow
  let z := coherentTerminalRoot p q eta
  obtain ⟨hp,hq,hpq⟩ := directFour_product_size ‖p‖ ‖q‖ hC hD
  have hz : z^2 = p*q+1 := coherent_analytic_terminal_root_sq p q eta
    (norm_pos_iff.mp hp) (norm_pos_iff.mp hq) heta
  have hrel := finite_tuple_root_relative_norm p q z hz hpq
  obtain ⟨hZ0,hZ,hZup⟩ := directFour_terminal_size ‖p‖ ‖q‖ ‖z‖ hp hD
    (norm_nonneg z) hrel.1 hrel.2
  change ∃ Z : ℝ, 0 < Z ∧ ‖p‖/2 < Z ∧ Z^2 ≤ 2*‖p‖*‖q‖ ∧
    1 < 13*‖v 1‖*‖v 2‖^2*‖v 3‖^3/Z+
      49*‖v 2‖*‖v 3‖^2*Z/(50*‖v 0‖*‖p‖^4)
  exact ⟨‖z‖,hZ0,hZ,hZup,hlow.trans_lt hforms.1⟩

end D1Bound5
end
