-- Prove2me | solution 1 for EulerMascheroni.Mixed.formal_e_functional_independence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:05:17.19821+00:00
-- url     : https://prove2.me/submissions/a665ec13-a785-4432-be8a-3700aad6fd9e

import Theorems.Thm_EulerMascheroni_Mixed_polynomial_exponential_wronskian
import Theorems.Thm_EulerMascheroni_Mixed_polynomial_logarithmic_wronskian
import Theorems.Thm_EulerMascheroni_Mixed_formal_e_system_equations
set_option autoImplicit false
set_option maxHeartbeats 2000000
open PowerSeries EulerMascheroni.Mixed
namespace EulerFormalSystem
lemma exponential_independent (p q : Polynomial ℂ)
    (h : (p:ℂ⟦X⟧)+(q:ℂ⟦X⟧)*exp ℂ=0) : p=0 ∧ q=0 := by
  have hd := congrArg (derivative ℂ) h
  simp only [map_add, derivative_coe, Derivation.leibniz, derivative_exp,
    smul_eq_mul, map_zero] at hd
  have hw : ((p.derivative*q-p*q.derivative-p*q : Polynomial ℂ):ℂ⟦X⟧)=0 := by
    push_cast
    linear_combination (q:ℂ⟦X⟧)*hd-
      ((q.derivative:ℂ⟦X⟧)+(q:ℂ⟦X⟧))*h
  have hw' := sub_eq_zero.mp (Polynomial.coe_eq_zero_iff.mp hw)
  rcases polynomial_exponential_wronskian p q hw' with hp | hq
  · refine ⟨hp,?_⟩
    simp only [hp,Polynomial.coe_zero,zero_add] at h
    exact Polynomial.coe_eq_zero_iff.mp
      ((mul_eq_zero.mp h).resolve_right (isUnit_exp ℂ).ne_zero)
  · refine ⟨?_,hq⟩
    simpa only [hq,Polynomial.coe_zero,zero_mul,add_zero,Polynomial.coe_eq_zero_iff] using h
lemma functional_independence (p q r : Polynomial ℂ)
    (h : (p:ℂ⟦X⟧)+(q:ℂ⟦X⟧)*exp ℂ+(r:ℂ⟦X⟧)*formalExpEin=0) :
    p=0 ∧ q=0 ∧ r=0 := by
  have hd := congrArg (derivative ℂ) h
  simp only [map_add, derivative_coe, Derivation.leibniz, derivative_exp,
    smul_eq_mul, map_zero] at hd
  let P : Polynomial ℂ := Polynomial.X*r*p.derivative-
    Polynomial.X*(r.derivative+r)*p-r^2
  let Q : Polynomial ℂ := Polynomial.X*(r*q.derivative-r.derivative*q)+r^2
  have hnew : (P:ℂ⟦X⟧)+(Q:ℂ⟦X⟧)*exp ℂ=0 := by
    dsimp [P,Q]
    push_cast
    linear_combination X*(r:ℂ⟦X⟧)*hd-
      X*((r.derivative:ℂ⟦X⟧)+(r:ℂ⟦X⟧))*h-
      (r:ℂ⟦X⟧)^2*(formal_e_system_equations.2.2)
  have hQ := (exponential_independent P Q hnew).2
  have hr : r=0 := by
    apply polynomial_logarithmic_wronskian r (-q)
    simp only [Polynomial.derivative_neg]
    dsimp [Q] at hQ
    linear_combination -hQ
  simp only [hr,Polynomial.coe_zero,zero_mul,add_zero] at h
  exact ⟨(exponential_independent p q h).1,(exponential_independent p q h).2,hr⟩
end EulerFormalSystem


theorem solution (p q r : Polynomial ℂ)
    (h : (p:ℂ⟦X⟧)+(q:ℂ⟦X⟧)*exp ℂ+(r:ℂ⟦X⟧)*formalExpEin=0) :
    p=0 ∧ q=0 ∧ r=0 := by
  exact EulerFormalSystem.functional_independence p q r h

#print axioms solution
