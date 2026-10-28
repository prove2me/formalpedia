-- Prove2me | solution 1 for D1Bound5.coherent_three_zero_bootstrap
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:42:41.802787+00:00
-- url     : https://prove2.me/submissions/994c903b-612c-4280-960c-6293002a8e51

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
import Definitions.Def_D1Bound5_CoherentFormBounds_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_coherentQuotientForm_zero_norm_relation
import Theorems.Thm_D1Bound5_coherentRemainder_norm_sub_le
import Theorems.Thm_D1Bound5_coherent_cpow_half_near_one
import Theorems.Thm_D1Bound5_coherent_half_binomial_manuscript_anchor_radius
import Theorems.Thm_D1Bound5_coherent_three_remainder_envelope

section
open Finset

namespace D1Bound5

/-- A zero actual three-anchor form forces a first terminal separation
without assuming Q≥4P. This is the bootstrap used before applying the
sharper separated vanishing window. -/
theorem _root_.solution
    (a : Fin 3 → ℂ) (hinj : Function.Injective a) (p q eta : ℂ)
    (A : ℝ) (hA : 0 < A) (ha : ∀ i, A ≤ ‖a i‖)
    (hP : 0 < ‖p‖) (hQ : ‖p‖ ≤ ‖q‖)
    (hAP : 9 ≤ A*‖p‖) (hPQ : 10000 < ‖p‖*‖q‖)
    (heta : eta^2 = p*q)
    (hL : coherentQuotientForm a (coherentVandermonde3 a) p q eta = 0) :
    (∏ i, ‖a i‖)*‖p‖^2 < ‖q‖ := by
  let P := ‖p‖
  let Q := ‖q‖
  let V := ∏ i, ‖a i‖
  let F := ‖coherentRemainder a p q‖
  let d := ‖1-(1+p⁻¹*q⁻¹)^(1/2 : ℂ)‖
  have hQ0 : 0 < Q := hP.trans_le hQ
  have hV : 0 < V := Finset.prod_pos (fun i _ => hA.trans_le (ha i))
  have hp0 : p ≠ 0 := norm_pos_iff.mp hP
  have hq0 : q ≠ 0 := norm_pos_iff.mp hQ0
  have heta0 : eta ≠ 0 := by
    intro hz
    rw [hz,zero_pow (by decide : (2 : ℕ) ≠ 0)] at heta
    exact mul_ne_zero hp0 hq0 heta.symm
  have han : ∀ i, a i ≠ 0 := fun i => norm_pos_iff.mp (hA.trans_le (ha i))
  have hDelta : coherentVandermonde3 a ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr (hinj.ne (by decide)))
        (sub_ne_zero.mpr (hinj.ne (by decide))))
      (sub_ne_zero.mpr (hinj.ne (by decide)))
  have hp : ‖p⁻¹‖ ≤ 1/P := by simp [P,norm_inv,one_div]
  have hq : ‖q⁻¹‖ ≤ 1/P := by
    simpa only [Q,norm_inv,one_div] using one_div_le_one_div_of_le hP hQ
  have hAP1 : 1 < A*P := by linarith only [hAP]
  have hxp (i : Fin 3) : ‖p⁻¹*(a i)⁻¹‖ < 1 :=
    coherent_half_binomial_manuscript_anchor_radius Finset.univ a p⁻¹ A P
      hA hP (fun j _ => ha j) hp hAP1 i (Finset.mem_univ i)
  have hxq (i : Fin 3) : ‖q⁻¹*(a i)⁻¹‖ < 1 :=
    coherent_half_binomial_manuscript_anchor_radius Finset.univ a q⁻¹ A P
      hA hP (fun j _ => ha j) hq hAP1 i (Finset.mem_univ i)
  have hrel : d = F/V := coherentQuotientForm_zero_norm_relation a (by decide)
    han hinj (coherentVandermonde3 a) p q eta hDelta heta0 hxp hxq hL
  have ht := coherentRemainder_norm_sub_le a (by decide) p q A P
    hA hP ha hp hq hAP1
  have he := coherent_three_remainder_envelope p⁻¹ q⁻¹ A P hA hP hp hq hAP
  have hF : F ≤ 1/(3*P^3) := by
    have hn := norm_add_le
      (coherentRemainder a p q-halfBinomialWeightedCoeff p⁻¹ q⁻¹ 3)
      (halfBinomialWeightedCoeff p⁻¹ q⁻¹ 3)
    rw [sub_add_cancel] at hn
    exact (hn.trans (add_le_add ht le_rfl)).trans (by simpa only [add_comm] using he)
  have hw : ‖p⁻¹*q⁻¹‖ = 1/(P*Q) := by
    simp [P,Q,norm_mul,norm_inv,one_div,mul_inv_rev,mul_comm]
  have hwsmall : ‖p⁻¹*q⁻¹‖ < (1/10000 : ℝ) := by
    rw [hw]
    exact one_div_lt_one_div_of_lt (by norm_num) hPQ
  have hnear := coherent_cpow_half_near_one (p⁻¹*q⁻¹)
    (mul_ne_zero (inv_ne_zero hp0) (inv_ne_zero hq0)) hwsmall
  have hd : 1/(3*P*Q) < d := by
    have hn := hnear.2.2.1
    rw [hw] at hn
    calc
      _ = (1/3 : ℝ)*(1/(P*Q)) := by ring
      _ < (100/201 : ℝ)*(1/(P*Q)) :=
        mul_lt_mul_of_pos_right (by norm_num) (by positivity)
      _ < d := hn
  have hquot : 1/(3*P*Q) < 1/(3*V*P^3) := by
    calc
      _ < d := hd
      _ = F/V := hrel
      _ ≤ (1/(3*P^3))/V := div_le_div_of_nonneg_right hF hV.le
      _ = _ := by ring
  have hc := (div_lt_div_iff₀
    (by positivity : 0 < 3*P*Q) (by positivity : 0 < 3*V*P^3)).mp hquot
  apply (mul_lt_mul_iff_of_pos_right (by positivity : 0 < 3*P)).mp
  nlinarith only [hc]

end D1Bound5
end
