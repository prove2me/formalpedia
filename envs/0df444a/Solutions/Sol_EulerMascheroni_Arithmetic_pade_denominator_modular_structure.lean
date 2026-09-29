-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.pade_denominator_modular_structure
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T21:11:03.953284+00:00
-- url     : https://prove2.me/submissions/fd5df534-c39c-4216-87d2-5abc834b511b

import Definitions.Def_eulerMascheroni_padeTransform
import Theorems.Thm_EulerMascheroni_Arithmetic_pade_binomial_identity
set_option autoImplicit false
set_option maxHeartbeats 1600000
open EulerMascheroni.Arithmetic
namespace PadeGcd
lemma q_closed (n : ℕ) :
    padeQ n = ∑ j ∈ Finset.range (n+1), (n.choose j : ℤ) * n.descFactorial (n-j) := by
  have hi := pade_binomial_identity 1 n
  have hz := pade_binomial_identity 0 n
  have hc : (padeQ n:ℝ) = (n.factorial:ℝ)^2 *
      ∑ j ∈ Finset.range (n+1), ((n.choose j * (n+j).choose n:ℕ):ℝ)/( (n+j).factorial:ℝ) := by
    have hh : binomialTransform (quotientCoeff 1) n - binomialTransform (quotientCoeff 0) n =
        ∑ j ∈ Finset.range (n+1), ((n.choose j * (n+j).choose n:ℕ):ℝ)/((n+j).factorial:ℝ) := by
      unfold binomialTransform
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      unfold quotientCoeff
      ring
    linear_combination hi - hz + (n.factorial:ℝ)^2*hh
  have hterm (j : ℕ) (hj : j ≤ n) :
      (n.factorial:ℝ)^2 * (((n.choose j * (n+j).choose n:ℕ):ℝ)/((n+j).factorial:ℝ)) =
        (n.choose j:ℝ)*(n.descFactorial (n-j):ℝ) := by
    have h1 : ((n+j).choose n:ℝ)*(n.factorial:ℝ)*(j.factorial:ℝ) = ((n+j).factorial:ℝ) := by
      exact_mod_cast (by simpa using Nat.choose_mul_factorial_mul_factorial (show n ≤ n+j by omega))
    have h2 : (j.factorial:ℝ)*(n.descFactorial (n-j):ℝ) = (n.factorial:ℝ) := by
      exact_mod_cast (by simpa [Nat.sub_sub_self hj] using
        Nat.factorial_mul_descFactorial (show n-j ≤ n by omega))
    have hfac : ((n+j).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+j)
    rw [← mul_div_assoc, div_eq_iff hfac]
    push_cast
    calc
      _ = (n.choose j:ℝ)*(n.descFactorial (n-j):ℝ)*
          (((n+j).choose n:ℝ)*(n.factorial:ℝ)*(j.factorial:ℝ)) := by
        linear_combination -(n.choose j:ℝ)*((n+j).choose n:ℝ)*(n.factorial:ℝ)*h2
      _ = _ := by rw [h1]
  have hr : (padeQ n:ℝ) = ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*(n.descFactorial (n-j):ℝ) := by
    rw [hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm j (by have := Finset.mem_range.mp hj; omega)
  exact_mod_cast hr

lemma q_mod_index (n : ℕ) : (n:ℤ) ∣ padeQ n - 1 := by
  rw [q_closed, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, Nat.descFactorial_zero, mul_one,
    add_sub_cancel_right]
  apply Finset.dvd_sum
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  have hd : n ∣ n.descFactorial (n-j) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    have he : k+1-j = (k-j)+1 := by omega
    rw [he, Nat.succ_descFactorial_succ]
    exact dvd_mul_right _ _
  exact dvd_mul_of_dvd_right (by exact_mod_cast hd) _

lemma q_adjacent_coprime (n : ℕ) : IsCoprime (padeQ n) (padeQ (n+1)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [padeQ, padeSeq]
    | succ n =>
      have hprev := ih n (by omega)
      have hqn : IsCoprime (padeQ (n+1)) ((n:ℤ)+1) := by
        obtain ⟨k, hk⟩ := q_mod_index (n+1)
        refine ⟨1, -k, ?_⟩
        push_cast at hk
        linear_combination hk
      have hp : IsCoprime (padeQ (n+1)) (((n:ℤ)+1)^2) := hqn.pow_right
      have hmul := hp.mul_right hprev.symm
      change IsCoprime (padeQ (n+1)) ((2*(n:ℤ)+4)*padeQ (n+1)-((n:ℤ)+1)^2*padeQ n)
      obtain ⟨a,b,hab⟩ := hmul
      refine ⟨a+b*(2*(n:ℤ)+4), -b, ?_⟩
      linear_combination hab

lemma q_periodic_mod (m : ℕ) (hm : 0 < m) (n : ℕ) :
    (padeQ (n+m) : ZMod m) = (padeQ n : ZMod m) := by
  have hqm : (padeQ m : ZMod m) = 1 := by
    obtain ⟨k, hk⟩ := q_mod_index m
    have hh := congrArg (fun z : ℤ => (z : ZMod m)) hk
    push_cast at hh
    exact sub_eq_zero.mp (by simpa using hh)
  have hqm1 : (padeQ (m+1) : ZMod m) = 2 := by
    have hrec : padeQ (m+1) = (2*((m-1:ℕ):ℤ)+4)*padeQ m -
        (((m-1:ℕ):ℤ)+1)^2*padeQ (m-1) := by
      have : m-1+2 = m+1 := by omega
      simpa only [this, Nat.sub_add_cancel hm] using
        (show padeQ (m-1+2) = (2*((m-1:ℕ):ℤ)+4)*padeQ (m-1+1)-
          (((m-1:ℕ):ℤ)+1)^2*padeQ (m-1) from rfl)
    have hcast : ((m-1:ℕ):ZMod m) + 1 = 0 := by
      have hh : m-1+1 = m := by omega
      have hc := congrArg (fun k : ℕ => (k : ZMod m)) hh
      simpa using hc
    rw [hrec]
    push_cast
    rw [hqm]
    linear_combination (2-(((m-1:ℕ):ZMod m)+1)*(padeQ (m-1):ZMod m))*hcast
  induction n using Nat.twoStepInduction with
  | zero => simpa [padeQ, padeSeq] using hqm
  | one => simpa [Nat.add_comm, padeQ, padeSeq] using hqm1
  | more n ih ih' =>
    have hrec (r : ℕ) : padeQ (r+2) = (2*(r:ℤ)+4)*padeQ (r+1)-((r:ℤ)+1)^2*padeQ r := rfl
    rw [show n+2+m = (n+m)+2 by omega, hrec (n+m), hrec n]
    push_cast
    rw [show n+m+1 = (n+1)+m by omega, ih, ih']
    simp

end PadeGcd


theorem solution (n : ℕ) :
    ((n:ℤ) ∣ padeQ n - 1) ∧ IsCoprime (padeQ n) (padeQ (n+1)) ∧
      ∀ m : ℕ, 0 < m → (padeQ (n+m) : ZMod m) = (padeQ n : ZMod m) := by
  exact ⟨PadeGcd.q_mod_index n, PadeGcd.q_adjacent_coprime n, fun m hm => PadeGcd.q_periodic_mod m hm n⟩
#print axioms solution
