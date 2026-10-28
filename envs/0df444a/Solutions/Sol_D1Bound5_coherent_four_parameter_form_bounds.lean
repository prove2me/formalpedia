-- Prove2me | solution 1 for D1Bound5.coherent_four_parameter_form_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:30:44.31382+00:00
-- url     : https://prove2.me/submissions/512aa54c-1b64-4919-9ede-afd31f6e5b66

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
import Definitions.Def_D1Bound5_CoherentFourParameters_Definitions
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Theorems.Thm_D1Bound5_coherentQuotientForm_norm_le_remainder
import Theorems.Thm_D1Bound5_coherentQuotientForm_zero_norm_relation
import Theorems.Thm_D1Bound5_coherentRemainder_four_parameter_norm_bounds
import Theorems.Thm_D1Bound5_coherent_cpow_half_near_one
import Theorems.Thm_D1Bound5_coherent_half_binomial_manuscript_anchor_radius
import Theorems.Thm_D1Bound5_coherent_three_parameter_upper_scalar
import Theorems.Thm_D1Bound5_coherent_three_window_scalar

section
open Finset

noncomputable section

namespace D1Bound5

















theorem coherent_four_parameter_comparisons :
    0 < coherentFourLowerConstant ∧ 0 < coherentFourUpperConstant ∧
    100*coherentFourUpperConstant/99 < (49/1200 : ℝ) ∧
    10 < 100/(201*coherentFourUpperConstant) ∧
    100/(199*coherentFourLowerConstant) < 17 := by
  norm_num [coherentFourLowerConstant,coherentFourUpperConstant,
    coherentFourLeadingLower,coherentFourLeadingUpper,coherentFourTailConstant]

end D1Bound5
end

section
open Finset

namespace D1Bound5

/-- The actual four-anchor form with its separated-parameter constants
and its exact zero-form window. -/
theorem _root_.solution
    (a : Fin 4 → ℂ) (hinj : Function.Injective a) (p q eta : ℂ)
    (A : ℝ) (hA : 0 < A) (ha : ∀ i, A ≤ ‖a i‖)
    (hP : 0 < ‖p‖) (hQ : 1000*‖p‖ ≤ ‖q‖) (hPQ : 10000 < ‖p‖*‖q‖)
    (hAP : 1000 ≤ A*‖p‖) (heta : eta^2 = p*q) :
    ‖coherentQuotientForm a (coherentVandermonde4 a) p q eta‖ <
        51*‖coherentVandermonde4 a‖/(100*‖coherentTerminalRoot p q eta‖) +
          (49/1200 : ℝ)*‖coherentVandermonde4 a‖*‖coherentTerminalRoot p q eta‖ /
            ((∏ i, ‖a i‖)*‖p‖^4) ∧
      (coherentQuotientForm a (coherentVandermonde4 a) p q eta = 0 →
        10*(∏ i, ‖a i‖)*‖p‖^3 < ‖q‖ ∧
          ‖q‖ < 17*(∏ i, ‖a i‖)*‖p‖^3) := by
  let P := ‖p‖
  let Q := ‖q‖
  let V := ∏ i, ‖a i‖
  let E := ‖eta‖
  let Z := ‖coherentTerminalRoot p q eta‖
  let D := ‖coherentVandermonde4 a‖
  let d := ‖1-(1+p⁻¹*q⁻¹)^(1/2 : ℂ)‖
  let F := ‖coherentRemainder a p q‖
  have han : ∀ i, a i ≠ 0 := fun i => norm_pos_iff.mp (hA.trans_le (ha i))
  have hV : 0 < V := Finset.prod_pos (fun i _ => hA.trans_le (ha i))
  have hQ0 : 0 < Q := by change 0 < ‖q‖; nlinarith only [hP,hQ]
  have hp0 : p ≠ 0 := norm_pos_iff.mp hP
  have hq0 : q ≠ 0 := norm_pos_iff.mp hQ0
  have heta0 : eta ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at heta
    exact (mul_ne_zero hp0 hq0) heta.symm
  have hE : 0 < E := norm_pos_iff.mpr heta0
  have hEsq : E^2 = P*Q := by
    simpa only [E,P,Q,norm_pow,norm_mul] using congrArg norm heta
  have hDelta : coherentVandermonde4 a ≠ 0 := by
    unfold coherentVandermonde4
    repeat' apply mul_ne_zero
    all_goals exact sub_ne_zero.mpr (hinj.ne (by decide))
  have hD : 0 < D := norm_pos_iff.mpr hDelta
  have hW : ‖p⁻¹*q⁻¹‖ = 1/(P*Q) := by
    simp [P,Q,norm_mul,norm_inv,one_div,mul_inv_rev,mul_comm]
  have hWsmall : ‖p⁻¹*q⁻¹‖ < (1/10000 : ℝ) := by
    rw [hW]
    exact one_div_lt_one_div_of_lt (by norm_num) hPQ
  have hnear := coherent_cpow_half_near_one (p⁻¹*q⁻¹)
    (mul_ne_zero (inv_ne_zero hp0) (inv_ne_zero hq0)) hWsmall
  have hZeq : Z = E*‖(1+p⁻¹*q⁻¹)^(1/2 : ℂ)‖ := by
    simp only [Z,E,coherentTerminalRoot,norm_mul]
  have hZlo : (99/100 : ℝ)*E < Z := by
    rw [hZeq]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hnear.1 hE
  have hZhi : Z < (101/100 : ℝ)*E := by
    rw [hZeq]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hnear.2.1 hE
  have hZ : 0 < Z := by nlinarith only [hZlo,hE]
  have hdlo : 100/(201*P*Q) < d := by
    have h := hnear.2.2.1
    rw [hW] at h
    calc
      _ = (100/201 : ℝ)*(1/(P*Q)) := by ring
      _ < _ := h
  have hdhi : d < 100/(199*P*Q) := by
    have h := hnear.2.2.2
    rw [hW] at h
    calc
      _ < (100/199 : ℝ)*(1/(P*Q)) := h
      _ = _ := by ring
  have hp : ‖p⁻¹‖ = 1/P := by simp [P,norm_inv,one_div]
  have hq : ‖q⁻¹‖ ≤ 1/(1000*P) := by
    simpa only [Q,norm_inv,one_div] using
      one_div_le_one_div_of_le (by positivity : 0 < 1000*P) hQ
  have hq' : ‖q⁻¹‖ ≤ 1/P := hq.trans
    (one_div_le_one_div_of_le hP (by change ‖p‖ ≤ 1000*‖p‖; nlinarith only [hP]))
  have hxp : ∀ i, ‖p⁻¹*(a i)⁻¹‖ < 1 := by
    intro i
    exact coherent_half_binomial_manuscript_anchor_radius Finset.univ a p⁻¹ A P
      hA hP (fun j _ => ha j) hp.le (by linarith) i (Finset.mem_univ i)
  have hxq : ∀ i, ‖q⁻¹*(a i)⁻¹‖ < 1 := by
    intro i
    exact coherent_half_binomial_manuscript_anchor_radius Finset.univ a q⁻¹ A P
      hA hP (fun j _ => ha j) hq' (by linarith) i (Finset.mem_univ i)
  obtain ⟨hFlo,hFhi⟩ := coherentRemainder_four_parameter_norm_bounds
    a p q A P hA hP ha hp hq hAP
  obtain ⟨hell,hu,hlam,hwindowLow,hwindowHigh⟩ := coherent_four_parameter_comparisons
  have hFlo' : coherentFourLowerConstant/P^3 ≤ P*F := by
    have h := mul_le_mul_of_nonneg_left hFlo hP.le
    have heq : P*(coherentFourLowerConstant/P^4) = coherentFourLowerConstant/P^3 := by
      field_simp <;> ring
    rwa [heq] at h
  have hFhi' : P*F ≤ coherentFourUpperConstant/P^3 := by
    have h := mul_le_mul_of_nonneg_left hFhi hP.le
    have heq : P*(coherentFourUpperConstant/P^4) = coherentFourUpperConstant/P^3 := by
      field_simp <;> ring
    rwa [heq] at h
  have hscale : (P*F)/(V*P) = F/V := by
    rw [mul_comm P F]
    exact mul_div_mul_right F V (show P ≠ 0 from ne_of_gt hP)
  have hL := coherentQuotientForm_norm_le_remainder a (by decide) han hinj
    (coherentVandermonde4 a) p q eta hDelta heta0 hxp hxq
  have hL' : ‖coherentQuotientForm a (coherentVandermonde4 a) p q eta‖ ≤
      D*E*(d+(P*F)/(V*P)) := by rw [hscale]; exact hL
  constructor
  · have h := coherent_three_parameter_upper_scalar (V*P) P Q E Z D d (P*F)
      ‖coherentQuotientForm a (coherentVandermonde4 a) p q eta‖
      coherentFourUpperConstant (49/1200) (mul_pos hV hP) hP hQ0 hE hZ hD hu
      hEsq hZlo hZhi hdhi hFhi' hlam hL'
    calc
      _ < 51*D/(100*Z)+(49/1200 : ℝ)*D*Z/((V*P)*P^3) := h
      _ = _ := by dsimp only [D,Z,V,P]; congr 1 <;> ring
  · intro hzero
    have hrel := coherentQuotientForm_zero_norm_relation a (by decide) han hinj
      (coherentVandermonde4 a) p q eta hDelta heta0 hxp hxq hzero
    have hrel' : d = (P*F)/(V*P) := by rw [hscale]; exact hrel
    have hw := coherent_three_window_scalar (V*P) P Q d (P*F)
      coherentFourLowerConstant coherentFourUpperConstant (mul_pos hV hP) hP hQ0
      hell hu hdlo hdhi hFlo' hFhi' hrel'
    constructor
    · calc
        10*V*P^3 < (100/(201*coherentFourUpperConstant))*V*P^3 := by
          have h := mul_lt_mul_of_pos_right hwindowLow (by positivity : 0 < V*P^3)
          nlinarith only [h]
        _ = 100*(V*P)*P^2/(201*coherentFourUpperConstant) := by ring
        _ < Q := hw.1
    · calc
        Q < 100*(V*P)*P^2/(199*coherentFourLowerConstant) := hw.2
        _ = (100/(199*coherentFourLowerConstant))*V*P^3 := by ring
        _ < 17*V*P^3 := by
          have h := mul_lt_mul_of_pos_right hwindowHigh (by positivity : 0 < V*P^3)
          nlinarith only [h]



end D1Bound5
end
