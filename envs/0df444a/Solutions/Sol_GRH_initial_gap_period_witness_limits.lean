-- Prove2me | solution 1 for GRH.initial_gap_period_witness_limits
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T16:16:22.161555+00:00
-- url     : https://prove2.me/submissions/b82b191f-1f86-43d9-86e0-5601bcc3bbce

import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-- When the real left edge is at most one, an initial-gap period witness
has a gap of length at most six, small totient, and no prime divisor above five. -/
theorem solution (Q M : ℕ) (a H : ℝ) (hQ : 2<Q) (ha : a ≤ 1)
    (gap : ∀ k : ℕ, 2 ≤ k → k ≤ M → ¬ k.Coprime Q)
    (test : (Q.totient:ℝ)/4*(1+Real.sqrt (1+(H/a)^2)) < ((M:ℝ)+1)^a) :
    M ≤ 6 ∧ Q.totient ≤ 13 ∧ ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ 5 := by
  have sqrt1 : 1 ≤ Real.sqrt (1+(H/a)^2) := by
    have e := Real.sq_sqrt (show 0 ≤ 1+(H/a)^2 by positivity)
    nlinarith [Real.sqrt_nonneg (1+(H/a)^2),sq_nonneg (H/a)]
  have lhs := mul_le_mul_of_nonneg_left (add_le_add_left sqrt1 1)
    (show 0 ≤ (Q.totient:ℝ)/4 by positivity)
  have rhs := Real.rpow_le_rpow_of_exponent_le
    (show 1 ≤ (M:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) M]) ha
  rw [Real.rpow_one] at rhs
  have bound : Q.totient < 2*(M+1) := by
    exact_mod_cast (show (Q.totient:ℝ) < 2*((M:ℝ)+1) by linarith)
  have mono {v : ℕ} (hv : v ∣ Q) : v.totient ≤ Q.totient :=
    Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) (Nat.totient_dvd_of_dvd hv)
  have divides {p : ℕ} (prime : p.Prime) (hle : p ≤ M) : p ∣ Q :=
    prime.dvd_iff_not_coprime.mpr (gap p prime.two_le hle)
  have prod {p : ℕ} (prime : p.Prime) (big : 5<p) (hp : p ∣ Q) (h5 : 5 ≤ M) :
      8*(p-1) ≤ Q.totient := by
    have c3 : Nat.Coprime 3 p := Nat.coprime_primes (by decide) prime |>.2 (by omega)
    have c5 : Nat.Coprime 5 p := Nat.coprime_primes (by decide) prime |>.2 (by omega)
    have c : Nat.Coprime 15 p := Nat.Coprime.mul_left c3 c5
    have h15 : 15 ∣ Q := (show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd
      (divides (by decide) (by omega)) (divides (by decide) h5)
    have h := mono (c.mul_dvd_of_dvd_of_dvd h15 hp)
    rwa [Nat.totient_mul c,Nat.totient_prime prime,show (15:ℕ).totient=8 by decide] at h
  have small : M ≤ 6 := by
    by_contra! large
    by_cases hm : M ≤ 15
    · have h := prod (p:=7) (by decide) (by decide) (divides (by decide) (by omega)) (by omega)
      omega
    · obtain ⟨p,hp,lower,upper⟩ := Nat.exists_prime_lt_and_le_two_mul (M/2) (by omega)
      have h := prod hp (by omega) (divides hp (by omega)) (by omega)
      omega
  refine ⟨small,by omega,?_⟩
  intro p prime hp
  by_contra! big
  have atLeast : 7 ≤ p := by
    have hn : p≠6 := fun h => (by decide : ¬ Nat.Prime 6) (h ▸ prime)
    omega
  have base := mono hp
  rw [Nat.totient_prime prime] at base
  by_cases h3 : M < 3
  · omega
  by_cases h5 : M < 5
  · have c : Nat.Coprime 3 p := (Nat.coprime_primes (by decide) prime).2 (by omega)
    have h := mono (c.mul_dvd_of_dvd_of_dvd (divides (by decide) (by omega)) hp)
    rw [Nat.totient_mul c,Nat.totient_prime prime,show (3:ℕ).totient=2 by decide] at h
    omega
  · have h := prod prime big hp (by omega)
    omega
