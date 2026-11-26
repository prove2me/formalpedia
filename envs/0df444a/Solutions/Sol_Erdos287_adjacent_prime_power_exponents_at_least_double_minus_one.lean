-- Prove2me | solution 1 for Erdos287.adjacent_prime_power_exponents_at_least_double_minus_one
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T06:05:37.545196+00:00
-- url     : https://prove2.me/submissions/62d0c771-7c8d-4b70-b20d-466a5e5c200a

import Mathlib

set_option autoImplicit false

/-- When fixed multiples of two distinct prime powers are adjacent twice, the
larger exponent of the first prime is at least twice the smaller minus one. -/
theorem solution (p q c d a b h j : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hc : 0 < c) (hd : 0 < d) (hh : 0 < h)
    (h₁ : |(c : ℤ) * (p : ℤ) ^ a - (d : ℤ) * (q : ℤ) ^ b| = 1)
    (h₂ : |(c : ℤ) * (p : ℤ) ^ (a + h) - (d : ℤ) * (q : ℤ) ^ (b + j)| = 1) :
    a ≤ h + 1 := by
  let U : ℤ := (c : ℤ) * (p : ℤ) ^ a
  let V : ℤ := (d : ℤ) * (q : ℤ) ^ b
  let R : ℤ := (p : ℤ) ^ h
  let S : ℤ := (q : ℤ) ^ j
  have hA : |U - V| = 1 := h₁
  have hB : |U * R - V * S| = 1 := by
    simpa only [pow_add, U, V, R, S, mul_assoc] using h₂
  have hcop := (((Nat.coprime_primes hp hq).mpr hpq).pow_left h).pow_right j
  have hne : R ≠ S := by
    intro he
    have heq : p ^ h = q ^ j := by exact_mod_cast (show (p : ℤ) ^ h = (q : ℤ) ^ j from he)
    rw [← heq] at hcop
    have hgt : 1 < p ^ h := one_lt_pow₀ hp.one_lt hh.ne'
    have heq1 : p ^ h = 1 := by simpa using hcop
    omega
  have hsmall : (1 : ℤ) ≤ |R - S| := by
    have hpos := abs_pos.mpr (sub_ne_zero.mpr hne)
    omega
  have hV : 0 ≤ V := mul_nonneg (by exact_mod_cast hd.le) (by positivity)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hidentity : V * (R - S) = (U * R - V * S) - (U - V) * R := by ring
  have hupper : V ≤ R + 1 := calc
    V = |V| * 1 := by rw [abs_of_nonneg hV, mul_one]
    _ ≤ |V| * |R - S| := mul_le_mul_of_nonneg_left hsmall (abs_nonneg V)
    _ = |(U * R - V * S) - (U - V) * R| := by rw [← abs_mul, hidentity]
    _ ≤ |U * R - V * S| + |(U - V) * R| := by
      simpa only [← sub_eq_add_neg, abs_neg] using abs_add_le (U * R - V * S) (-((U - V) * R))
    _ = R + 1 := by rw [hB, abs_mul, hA, abs_of_nonneg hR, one_mul, add_comm]
  have hdiff : U - V ≤ 1 := hA ▸ le_abs_self (U - V)
  have hlow : (p : ℤ) ^ a ≤ U := by
    have hc' : (1 : ℤ) ≤ c := by exact_mod_cast hc
    simpa only [U, one_mul] using
      mul_le_mul_of_nonneg_right hc' (show 0 ≤ (p : ℤ) ^ a by positivity)
  by_contra! hbad
  have hp₂ : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hR₁ : 1 ≤ R := one_le_pow₀ (by omega : (1 : ℤ) ≤ p)
  have hpow : (p : ℤ) ^ (h + 2) ≤ (p : ℤ) ^ a :=
    pow_le_pow_right₀ (by omega) (by omega)
  have hsq : (4 : ℤ) ≤ (p : ℤ) ^ 2 := by
    simpa only [show (2 : ℤ) ^ 2 = 4 by decide] using pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 2) hp₂ 2
  have hfour := mul_le_mul_of_nonneg_left hsq hR
  rw [show (p : ℤ) ^ (h + 2) = R * (p : ℤ) ^ 2 from pow_add _ _ _] at hpow
  linarith only [hfour, hpow, hR₁, hlow, hdiff, hupper]

