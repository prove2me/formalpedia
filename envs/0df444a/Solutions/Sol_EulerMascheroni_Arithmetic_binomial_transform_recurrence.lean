-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.binomial_transform_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T14:48:37.530041+00:00
-- url     : https://prove2.me/submissions/b49644f0-3450-4e40-9fb7-09172af8163e

import Definitions.Def_eulerMascheroni_padeTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EulerLegendre
noncomputable def w (n k : ℕ) : ℝ := (n.choose k:ℝ)*((n+k).choose n:ℝ)
lemma w_zero (n : ℕ) : w n 0 = 1 := by simp [w]
lemma w_vanish {n k : ℕ} (h : n < k) : w n k = 0 := by simp [w, Nat.choose_eq_zero_of_lt h]
lemma w_factorial {n k : ℕ} (h : k ≤ n) :
    w n k = ((n+k).factorial:ℝ)/((k.factorial:ℝ)^2*((n-k).factorial:ℝ)) := by
  rw [w, Nat.cast_choose ℝ h, Nat.cast_choose ℝ (by omega : n ≤ n+k)]
  simp only [Nat.add_sub_cancel_left]
  field_simp
  <;> ring

lemma raising_coeff (n k : ℕ) :
    ((n:ℝ)+1)*w (n+1) (k+1) =
      ((n:ℝ)+1+2*((k:ℝ)+1))*w n (k+1) +
        (2*(n:ℝ)+2*((k:ℝ)+1))*w n k := by
  rcases lt_trichotomy k n with h | h | h
  · rw [w_factorial (by omega : k+1 ≤ n+1), w_factorial (by omega : k+1 ≤ n),
      w_factorial (by omega : k ≤ n)]
    have hd : n-k = (n-(k+1))+1 := by omega
    have he : n+1-(k+1) = n-k := by omega
    have ha : n+1+(k+1) = (n+k)+1+1 := by omega
    have hb : n+(k+1) = (n+k)+1 := by omega
    rw [he,ha,hb,hd]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hc : (n:ℝ) = (n-(k+1):ℕ)+(k:ℝ)+1 := by
      exact_mod_cast (show n = (n-(k+1))+k+1 by omega)
    field_simp
    rw [hc]
    ring
  · subst n
    rw [w_vanish (by omega : k < k+1), w_factorial (by omega : k+1 ≤ k+1),
      w_factorial (by omega : k ≤ k)]
    simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_zero, zero_add, mul_one]
    rw [show k+1+(k+1) = (k+k)+1+1 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring
  · rw [w_vanish (by omega : n+1 < k+1), w_vanish (by omega : n < k+1), w_vanish h]
    ring

lemma lowering_coeff (n k : ℕ) :
    ((n:ℝ)+1-2*((k:ℝ)+1))*w (n+1) (k+1) =
      ((n:ℝ)+1)*w n (k+1) -
        (2*((n:ℝ)+2-((k:ℝ)+1)))*w (n+1) k := by
  by_cases h : k ≤ n
  · rw [w_factorial (by omega : k+1 ≤ n+1), w_factorial (by omega : k ≤ n+1)]
    by_cases hkn : k < n
    · rw [w_factorial (by omega : k+1 ≤ n)]
      have h1 : n+1-(k+1) = (n-(k+1))+1 := by omega
      have h2 : n+1-k = (n-(k+1))+1+1 := by omega
      rw [h1,h2, show n+1+(k+1)=(n+k)+1+1 by omega,
        show n+(k+1)=(n+k)+1 by omega, show n+1+k=(n+k)+1 by omega]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hc : (n:ℝ) = (n-(k+1):ℕ)+(k:ℝ)+1 := by
        exact_mod_cast (show n = (n-(k+1))+k+1 by omega)
      field_simp
      rw [hc]
      ring
    · have : k=n := by omega
      subst k
      rw [w_vanish (by omega : n < n+1)]
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_zero, mul_one]
      rw [show n+1-n=1 by omega, show n+1+(n+1)=(n+n)+1+1 by omega,
        show n+1+n=(n+n)+1 by omega]
      simp only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
      <;> ring
  · by_cases hlast : k = n+1
    · subst k
      rw [w_vanish (by omega : n+1 < n+1+1), w_vanish (by omega : n < n+1+1)]
      push_cast
      ring
    · rw [w_vanish (by omega : n+1 < k+1), w_vanish (by omega : n < k+1),
        w_vanish (by omega : n+1 < k)]
      ring
end EulerLegendre

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial
namespace EulerLegendre
noncomputable def L (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n+1), C (w n k) * X^k
lemma coeff_L (n k : ℕ) : (L n).coeff k = w n k := by
  simp only [L, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases h : k < n+1
  · simp [h]
  · simp [h, w_vanish (by omega : n < k)]
lemma coeff_X_derivative (p : ℝ[X]) (k : ℕ) :
    (X*p.derivative).coeff k = (k:ℝ)*p.coeff k := by
  cases k with
  | zero => simp
  | succ k => simp [coeff_X_mul, coeff_derivative, mul_comm]
lemma raising (n : ℕ) :
    C ((n:ℝ)+1)*L (n+1) =
      C ((n:ℝ)+1)*(1+2*X)*L n + 2*X*(1+X)*(L n).derivative := by
  have he : C ((n:ℝ)+1)*(1+2*X)*L n + 2*X*(1+X)*(L n).derivative =
      C ((n:ℝ)+1)*L n + C (2*((n:ℝ)+1))*(X*L n) +
      C 2*(X*(L n).derivative) + C 2*(X*(X*(L n).derivative)) := by
    simp only [map_mul, map_add, map_ofNat, map_natCast, map_one]
    ring
  rw [he]
  ext k
  cases k with
  | zero => simp [coeff_L, w_zero, coeff_X_derivative]
  | succ k =>
    simp only [coeff_C_mul, coeff_add, coeff_X_mul, coeff_X_derivative, coeff_derivative, coeff_L]
    push_cast
    linear_combination raising_coeff n k
lemma lowering (n : ℕ) :
    C ((n:ℝ)+1)*((1+2*X)*L (n+1)-L n) =
      2*X*(1+X)*(L (n+1)).derivative := by
  have hleft : C ((n:ℝ)+1)*((1+2*X)*L (n+1)-L n) =
      C ((n:ℝ)+1)*L (n+1)+C (2*((n:ℝ)+1))*(X*L (n+1))-
        C ((n:ℝ)+1)*L n := by
    simp only [map_mul, map_add, map_ofNat, map_natCast, map_one]
    ring
  have hright : 2*X*(1+X)*(L (n+1)).derivative =
      C 2*(X*(L (n+1)).derivative)+C 2*(X*(X*(L (n+1)).derivative)) := by
    simp only [map_ofNat]
    ring
  rw [hleft,hright]
  ext k
  cases k with
  | zero => simp [coeff_L, w_zero, coeff_X_derivative]
  | succ k =>
    simp only [coeff_C_mul, coeff_add, coeff_sub, coeff_X_mul, coeff_X_derivative, coeff_derivative, coeff_L]
    push_cast
    linear_combination lowering_coeff n k
lemma recurrence (n : ℕ) :
    C ((n:ℝ)+2)*L (n+2) =
      C (2*(n:ℝ)+3)*(1+2*X)*L (n+1)-C ((n:ℝ)+1)*L n := by
  have h1 := raising (n+1)
  have h2 := lowering n
  push_cast at h1
  simp only [map_add, map_mul, map_ofNat, map_natCast, map_one] at h1 h2 ⊢
  linear_combination h1-h2
lemma eval_L_neg_one (n : ℕ) : (L n).eval (-1) = (-1:ℝ)^n := by
  induction n with
  | zero => simp [L,w]
  | succ n ih =>
    have h := congrArg (Polynomial.eval (-1:ℝ)) (raising n)
    simp only [eval_mul, eval_C, eval_add, eval_one, eval_ofNat, eval_X, ih] at h
    rw [pow_succ]
    nlinarith
noncomputable def B (n : ℕ) : ℝ[X] := X^n*L n
lemma X_derivative_B (n : ℕ) :
    X*(B n).derivative = C (n:ℝ)*B n+X^(n+1)*(L n).derivative := by
  cases n with
  | zero => simp [B]
  | succ n =>
    rw [B, derivative_mul, derivative_X_pow_succ]
    simp only [B, pow_succ]
    push_cast
    ring
lemma B_recurrence (n : ℕ) :
    C ((n:ℝ)+2)*B (n+2) =
      X*(C (2*(n:ℝ)+3)*(1+2*X)*B (n+1)-C ((n:ℝ)+1)*X*B n) := by
  have h := recurrence n
  dsimp [B]
  simp only [pow_succ]
  linear_combination X^n*X^2*h
lemma B_lowering (n : ℕ) :
    2*X*(1+X)*(B (n+1)).derivative =
      C ((n:ℝ)+1)*((3+4*X)*B (n+1)-X*B n) := by
  have h1 := X_derivative_B (n+1)
  have h2 := lowering n
  simp only [B, pow_succ, Nat.cast_add, Nat.cast_one, map_add, map_one,
    map_ofNat, map_mul] at h1 h2 ⊢
  linear_combination 2*(1+X)*h1 - X^n*X*h2
lemma B_raising (n : ℕ) :
    2*X^2*(1+X)*(B n).derivative =
      X*(C ((n:ℝ)-1)-2*X)*B n+C ((n:ℝ)+1)*B (n+1) := by
  have h1 := X_derivative_B n
  have h2 := raising n
  simp only [B, pow_succ, Nat.cast_add, Nat.cast_one, map_add, map_sub, map_one,
    map_ofNat, map_mul] at h1 h2 ⊢
  linear_combination 2*X*(1+X)*h1 - X^n*X*h2
lemma eval_B_neg_one (n : ℕ) : (B n).eval (-1) = 1 := by
  simp only [B, eval_mul, eval_pow, eval_X, eval_L_neg_one, ← mul_pow]
  norm_num
end EulerLegendre

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial
namespace EulerLegendre
noncomputable def moment (f : ℕ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun n => LinearMap.toSpanSingleton ℝ ℝ (f n))
lemma moment_monomial (f : ℕ → ℝ) (n : ℕ) (a : ℝ) :
    moment f (monomial n a) = a*f n := by
  simp [moment, Polynomial.lsum, Polynomial.sum_monomial_index]
lemma moment_C_mul_X_pow (f : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    moment f (C a*X^n) = a*f n := by
  rw [C_mul_X_pow_eq_monomial, moment_monomial]
lemma moment_C_mul (f : ℕ → ℝ) (a : ℝ) (p : ℝ[X]) :
    moment f (C a*p) = a*moment f p := by
  rw [← smul_eq_C_mul, map_smul]
  rfl
lemma moment_recurrence (f : ℕ → ℝ)
    (hf : ∀ k : ℕ, ((k+1:ℕ):ℝ)*f (k+1)=f k-(-1:ℝ)^k)
    (p : ℝ[X]) :
    moment f (X^2*p.derivative+(X-1)*p) = -p.eval (-1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [derivative_add, mul_add, add_add_add_comm, map_add, eval_add] at hp hq ⊢
    linarith
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial]
    cases n with
    | zero =>
      simp only [pow_zero, mul_one, derivative_C, mul_zero, zero_add]
      have he : (X-1)*C a = C a*X^1-C a*X^0 := by ring
      rw [he, map_sub, moment_C_mul_X_pow, moment_C_mul_X_pow]
      simp only [eval_C]
      have hh := hf 0
      norm_num at hh
      linear_combination a*hh
    | succ n =>
      simp only [derivative_C_mul, derivative_X_pow_succ]
      have he : X^2*(C a*(C ((n:ℝ)+1)*X^n))+(X-1)*(C a*X^(n+1)) =
          C (a*((n:ℝ)+2))*X^(n+2)-C a*X^(n+1) := by
        simp only [map_mul, map_add, map_ofNat, map_natCast, map_one, pow_succ]
        ring
      push_cast
      rw [he, map_sub, moment_C_mul_X_pow, moment_C_mul_X_pow]
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      have hh := hf (n+1)
      push_cast at hh
      linear_combination a*hh
end EulerLegendre

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Polynomial
namespace EulerLegendre
noncomputable def certificate (n : ℕ) : ℝ[X] :=
  (C (3*(n:ℝ)+7)+C (4*(n:ℝ)+6)*X)*B (n+1)-
    (C 2+C ((n:ℝ)+1)*X)*B n
lemma certificate_identity (n : ℕ) :
    X^2*(certificate n).derivative+(X-1)*certificate n =
      C 2*(C (((n:ℝ)+2)^2)*B (n+2)-C (2*(n:ℝ)+4)*B (n+1)+B n) := by
  have hn : (2*(1+X):ℝ[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p : ℝ[X] => p.coeff 0) h
    norm_num at this
  apply mul_left_cancel₀ hn
  have hR := B_raising n
  have hL := B_lowering n
  have hC := B_recurrence n
  simp only [certificate, derivative_mul, derivative_add, derivative_sub,
    derivative_C, derivative_X, zero_mul, zero_add, mul_one]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one] at hR hL hC ⊢
  linear_combination
    (3*(n:ℝ[X])+7+(4*(n:ℝ[X])+6)*X)*X*hL -
    (2+((n:ℝ[X])+1)*X)*hR - 4*(1+X)*((n:ℝ[X])+2)*hC
lemma certificate_eval (n : ℕ) : (certificate n).eval (-1) = 0 := by
  simp only [certificate, eval_mul, eval_C, eval_sub, eval_add, eval_X,
    eval_ofNat, eval_B_neg_one]
  ring
lemma moment_B (f : ℕ → ℝ) (n : ℕ) :
    moment f (B n) = EulerMascheroni.Arithmetic.binomialTransform f n := by
  have he : B n = ∑ j ∈ Finset.range (n+1), C (w n j)*X^(n+j) := by
    simp only [B,L,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add]
    ring
  rw [he, map_sum]
  simp only [moment_C_mul_X_pow, EulerMascheroni.Arithmetic.binomialTransform, w, Nat.cast_mul]
lemma transform_recurrence (f : ℕ → ℝ)
    (hf : ∀ k : ℕ, ((k+1:ℕ):ℝ)*f (k+1)=f k-(-1:ℝ)^k) (n : ℕ) :
    ((n:ℝ)+2)^2*EulerMascheroni.Arithmetic.binomialTransform f (n+2) =
      (2*(n:ℝ)+4)*EulerMascheroni.Arithmetic.binomialTransform f (n+1)-
        EulerMascheroni.Arithmetic.binomialTransform f n := by
  have h := moment_recurrence f hf (certificate n)
  simp only [certificate_identity, certificate_eval, neg_zero, moment_C_mul, map_add, map_sub,
    moment_B] at h
  simp only [← C_add, moment_C_mul, moment_B] at h
  linarith
end EulerLegendre

theorem solution
    (f : ℕ → ℝ)
    (hf : ∀ k : ℕ, ((k+1 : ℕ) : ℝ)*f (k+1) = f k - (-1 : ℝ)^k)
    (n : ℕ) :
    ((n:ℝ)+2)^2 * EulerMascheroni.Arithmetic.binomialTransform f (n+2) =
      (2*(n:ℝ)+4) * EulerMascheroni.Arithmetic.binomialTransform f (n+1) -
        EulerMascheroni.Arithmetic.binomialTransform f n := by
  exact EulerLegendre.transform_recurrence f hf n

#print axioms solution
