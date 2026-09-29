-- Prove2me | solution 1 for EulerMascheroni.Mixed.polynomial_exponential_wronskian
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:05:14.322138+00:00
-- url     : https://prove2.me/submissions/7ca4483e-26be-40c6-be80-5265b6ad87f4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial
namespace EulerPolynomial
lemma exponential_wronskian (p q : ℂ[X])
    (h : p.derivative*q-p*q.derivative=p*q) : p=0 ∨ q=0 := by
  by_contra hn
  push Not at hn
  have hp : p.derivative.natDegree ≤ p.natDegree := (natDegree_derivative_le p).trans (Nat.sub_le _ _)
  have hq : q.derivative.natDegree ≤ q.natDegree := (natDegree_derivative_le q).trans (Nat.sub_le _ _)
  have he := congrArg (fun r : ℂ[X] => r.coeff (p.natDegree+q.natDegree)) h
  rw [coeff_sub, coeff_mul_add_eq_of_natDegree_le hp le_rfl,
    coeff_mul_add_eq_of_natDegree_le le_rfl hq,
    coeff_mul_add_eq_of_natDegree_le le_rfl le_rfl] at he
  have hpd : p.derivative.coeff p.natDegree=0 := by
    rw [coeff_derivative,coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < p.natDegree+1)]
    ring
  have hqd : q.derivative.coeff q.natDegree=0 := by
    rw [coeff_derivative,coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < q.natDegree+1)]
    ring
  simp only [hpd,hqd,zero_mul,mul_zero,sub_zero] at he
  exact (mul_ne_zero (leadingCoeff_ne_zero.mpr hn.1) (leadingCoeff_ne_zero.mpr hn.2)) he.symm
lemma factor_at_zero (p : ℂ[X]) (hp : p ≠ 0) :
    ∃ m : ℕ, ∃ r : ℂ[X], p=X^m*r ∧ r.coeff 0 ≠ 0 := by
  obtain ⟨r,hr⟩ := (X_pow_dvd_iff.mpr (fun d hd =>
    coeff_eq_zero_of_lt_natTrailingDegree hd) : (X:ℂ[X])^p.natTrailingDegree ∣ p)
  refine ⟨p.natTrailingDegree,r,hr,?_⟩
  intro hz
  apply (coeff_natTrailingDegree_ne_zero.mpr hp)
  calc
    p.coeff p.natTrailingDegree = (X^p.natTrailingDegree*r).coeff p.natTrailingDegree :=
      congrArg (fun a : ℂ[X] => a.coeff p.natTrailingDegree) hr
    _ = r.coeff 0 := by simpa only [Nat.zero_add] using coeff_X_pow_mul r p.natTrailingDegree 0
    _ = 0 := hz
lemma X_derivative_factor (m : ℕ) (r : ℂ[X]) :
    X*(X^m*r).derivative = X^m*(C (m:ℂ)*r+X*r.derivative) := by
  cases m with
  | zero => simp
  | succ m =>
    rw [derivative_mul,derivative_X_pow_succ]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    ring
lemma log_equation_forces_q_zero_at_zero (p q : ℂ[X]) (hp : p ≠ 0)
    (hp0 : p.coeff 0=0) (h : X*(p*q.derivative-p.derivative*q)=p^2) : q.coeff 0=0 := by
  obtain ⟨m,r,hr,hr0⟩ := factor_at_zero p hp
  have hm : m ≠ 0 := by
    intro hm
    simp [hr,hm] at hp0
    exact hr0 hp0
  have hx : (X:ℂ[X])^m ≠ 0 := pow_ne_zero _ X_ne_zero
  have hh : X*r*q.derivative-(C (m:ℂ)*r+X*r.derivative)*q = X^m*r^2 := by
    apply mul_left_cancel₀ hx
    have hd := X_derivative_factor m r
    rw [hr] at h
    linear_combination h + q*hd
  have he := congrArg (fun s : ℂ[X] => s.eval 0) hh
  simp only [eval_mul,eval_X,zero_mul,eval_sub,zero_sub,eval_add,eval_C,eval_pow,
    zero_pow hm,add_zero,mul_zero] at he
  have hmC : (m:ℂ) ≠ 0 := by exact_mod_cast hm
  have he0 : (m:ℂ)*r.coeff 0*q.coeff 0=0 := by simpa only [← coeff_zero_eq_eval_zero, neg_eq_zero] using he
  exact (mul_eq_zero.mp he0).resolve_left (mul_ne_zero hmC hr0)
lemma logarithmic_wronskian (p q : ℂ[X])
    (h : X*(p*q.derivative-p.derivative*q)=p^2) : p=0 := by
  have main : ∀ N : ℕ, ∀ p q : ℂ[X], p.natDegree=N →
      X*(p*q.derivative-p.derivative*q)=p^2 → p=0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro p q hN heq
      by_contra hp
      have hp0 : p.coeff 0=0 := by
        have hh := congrArg (fun s : ℂ[X] => s.eval 0) heq
        simpa only [← coeff_zero_eq_eval_zero] using (sq_eq_zero_iff.mp (show (p.eval 0)^2=0 by simpa using hh.symm))
      have hq0 := log_equation_forces_q_zero_at_zero p q hp hp0 heq
      obtain ⟨r,hr⟩ := X_dvd_iff.mpr hp0
      obtain ⟨s,hs⟩ := X_dvd_iff.mpr hq0
      have hrn : r ≠ 0 := by intro hh; simp [hr,hh] at hp
      have hrs : X*(r*s.derivative-r.derivative*s)=r^2 := by
        apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero : (X:ℂ[X]) ≠ 0))
        rw [hr,hs,derivative_mul,derivative_mul,derivative_X] at heq
        linear_combination heq
      have hlt : r.natDegree < N := by
        rw [hr,natDegree_X_mul hrn] at hN
        omega
      exact hrn (ih r.natDegree hlt r s rfl hrs)
  exact main p.natDegree p q rfl h
end EulerPolynomial


theorem solution (p q : ℂ[X])
    (h : p.derivative*q-p*q.derivative=p*q) : p=0 ∨ q=0 := by
  exact EulerPolynomial.exponential_wronskian p q h

#print axioms solution
