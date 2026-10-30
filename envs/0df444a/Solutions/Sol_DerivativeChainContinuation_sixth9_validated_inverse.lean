-- Prove2me | solution 1 for DerivativeChainContinuation.sixth9_validated_inverse
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T04:39:51.037883+00:00
-- url     : https://prove2.me/submissions/b3ac505c-ea06-43f7-9a94-87cf5cf4a746

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FinitePolynomialContraction
import Definitions.Def_DerivativeChainContinuation_Sixth9C0Data
import Definitions.Def_DerivativeChainContinuation_Sixth9C1Data
import Definitions.Def_DerivativeChainContinuation_Sixth9C2Data
import Definitions.Def_DerivativeChainContinuation_Sixth9C3Data
import Definitions.Def_DerivativeChainContinuation_Sixth9InversePolynomial
import Definitions.Def_DerivativeChainContinuation_Sixth9PData
import Definitions.Def_DerivativeChainContinuation_Sixth9QData
import Definitions.Def_DerivativeChainContinuation_Sixth9ValidatedInverse
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_finite_polynomial_contraction
import Theorems.Thm_DerivativeChainContinuation_sixth9_coefficient_bound_0
import Theorems.Thm_DerivativeChainContinuation_sixth9_coefficient_bound_1
import Theorems.Thm_DerivativeChainContinuation_sixth9_coefficient_bound_2
import Theorems.Thm_DerivativeChainContinuation_sixth9_coefficient_bound_3
import Theorems.Thm_DerivativeChainContinuation_sixth9_newton_identity_0
import Theorems.Thm_DerivativeChainContinuation_sixth9_newton_identity_1
import Theorems.Thm_DerivativeChainContinuation_sixth9_newton_identity_2
import Theorems.Thm_DerivativeChainContinuation_sixth9_newton_identity_3
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open scoped BigOperators





theorem sixth9_newton_shift_identity (t y : ℂ) :
    sixth9Q t*sixth9G t (sixth9P t+y)=y-polynomialContractionMap 3 sixth9NewtonCoefficients t y := by
  have h0 := sixth9_newton_identity_0 t
  have h1 := sixth9_newton_identity_1 t
  have h2 := sixth9_newton_identity_2 t
  have h3 := sixth9_newton_identity_3 t
  norm_num [polynomialContractionMap,sixth9NewtonCoefficients,Fin.sum_univ_succ]
  dsimp only [sixth9G] at h0 ⊢
  linear_combination h0+y*h1+y^2*h2+y^3*h3

theorem sixth9_inverse_nonzero (t : ℂ) (ht : ‖t‖ ≤ 2) : sixth9Q t ≠ 0 := by
  intro h
  have hh := sixth9_newton_identity_1 t
  rw [h,zero_mul] at hh
  have hc : sixth9C1 t=1 := by linear_combination hh
  have hb := sixth9_coefficient_bound_1 t ht
  rw [hc,norm_one] at hb
  norm_num at hb


end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation

theorem validated_polynomial_branch (d : ℕ) (c : Fin (d+1) → ℂ → ℂ)
    (B : Fin (d+1) → ℝ) (P Q : ℂ → ℂ) (G : ℂ → ℂ → ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 ≤ M) (hB : ∀ j,0 ≤ B j)
    (hc : ∀ j,Differentiable ℂ (c j)) (hP : Differentiable ℂ P)
    (hbound : ∀ t : ℂ,‖t‖ ≤ R → ∀ j,‖c j t‖ ≤ B j)
    (hmap : (∑ j,B j*M^j.val) ≤ M)
    (hcontract : (∑ j,B j*(j.val:ℝ)*M^(j.val-1)) ≤ 1/2)
    (hreal : ∀ j,∀ x : ℝ,(c j (x:ℂ)).im=0)
    (hPreal : ∀ x : ℝ,(P (x:ℂ)).im=0)
    (hQ : ∀ t : ℂ,‖t‖ ≤ R → Q t ≠ 0)
    (hidentity : ∀ t y : ℂ,Q t*G t (P t+y)=y-polynomialContractionMap d c t y) :
    ∃ W : ℂ → ℂ,
      (∀ t : ℂ,‖t‖ ≤ R → ‖W t-P t‖ ≤ M ∧ G t (W t)=0) ∧
      DifferentiableOn ℂ W (Metric.ball 0 R) ∧
      ∀ x : ℝ,|x| ≤ R → (W (x:ℂ)).im=0 := by
  obtain ⟨Y,hY,hhol,hYr⟩ := finite_polynomial_contraction d c B R M hR hM hB hc hbound hmap hcontract hreal
  refine ⟨(fun t => P t+Y t),?_,hP.differentiableOn.add hhol,?_⟩
  · intro t ht
    refine ⟨by simpa only [add_sub_cancel_left] using (hY t ht).1,?_⟩
    have hh := hidentity t (Y t)
    rw [(hY t ht).2,sub_self] at hh
    exact (mul_eq_zero.mp hh).resolve_left (hQ t ht)
  · intro x hx
    simp only [Complex.add_im,hPreal,hYr x hx,add_zero]
end DerivativeChainContinuation

theorem solution :
    ∃ W : ℂ → ℂ,
      (∀ t : ℂ,‖t‖ ≤ 2 → ‖W t-sixth9P t‖ ≤ 1/100000000 ∧ sixth9G t (W t)=0) ∧
      DifferentiableOn ℂ W (Metric.ball 0 2) ∧
      ∀ x : ℝ,|x| ≤ 2 → (W (x:ℂ)).im=0 := by
  apply validated_polynomial_branch 3 sixth9NewtonCoefficients sixth9NewtonBounds sixth9P sixth9Q
    sixth9G 2 (1/100000000) (by norm_num) (by norm_num)
  · intro j; fin_cases j <;> norm_num [sixth9NewtonBounds]
  · intro j
    fin_cases j
    · change Differentiable ℂ sixth9C0
      unfold sixth9C0
      fun_prop
    · change Differentiable ℂ sixth9C1
      unfold sixth9C1
      fun_prop
    · change Differentiable ℂ sixth9C2
      unfold sixth9C2
      fun_prop
    · change Differentiable ℂ sixth9C3
      unfold sixth9C3
      fun_prop
  · unfold sixth9P; fun_prop
  · intro t ht j
    fin_cases j
    · exact sixth9_coefficient_bound_0 t ht
    · exact sixth9_coefficient_bound_1 t ht
    · exact sixth9_coefficient_bound_2 t ht
    · exact sixth9_coefficient_bound_3 t ht
  · norm_num [sixth9NewtonBounds,Fin.sum_univ_succ]
  · norm_num [sixth9NewtonBounds,Fin.sum_univ_succ]
  · intro j x
    fin_cases j <;> simp [sixth9NewtonCoefficients,sixth9C0,sixth9C1,sixth9C2,sixth9C3,← Complex.ofReal_pow]
  · intro x
    simp [sixth9P,← Complex.ofReal_pow]
  · exact sixth9_inverse_nonzero
  · exact sixth9_newton_shift_identity
