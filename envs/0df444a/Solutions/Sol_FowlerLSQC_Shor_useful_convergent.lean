-- Prove2me | solution 1 for FowlerLSQC.Shor.useful_convergent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T16:00:31.110496+00:00
-- url     : https://prove2.me/submissions/c5886a25-77ad-47d5-a101-7396575ad69e

import Mathlib
import Definitions.Def_FowlerLSQC_Shor_binaryLength
import Definitions.Def_FowlerLSQC_Shor_period

set_option autoImplicit false

namespace FowlerLSQC.ShorAux

/-- For distinct primes `p ≠ q`, `2 * lcm (p-1) (q-1) ≤ p * q`. -/
theorem two_lcm_le (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    2 * Nat.lcm (p - 1) (q - 1) ≤ p * q := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hl : Nat.lcm (p - 1) (q - 1) ≤ (p - 1) * (q - 1) := by
    have h1 : 0 < (p - 1) * (q - 1) := Nat.mul_pos (by omega) (by omega)
    exact Nat.le_of_dvd h1 (Nat.lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _))
  by_cases hp2' : p = 2
  · subst hp2'
    have : (2 - 1) * (q - 1) = q - 1 := by omega
    rw [this] at hl
    calc 2 * Nat.lcm (2 - 1) (q - 1) ≤ 2 * (q - 1) := by omega
      _ ≤ 2 * q := by omega
  by_cases hq2' : q = 2
  · subst hq2'
    have : (p - 1) * (2 - 1) = p - 1 := by omega
    rw [this] at hl
    calc 2 * Nat.lcm (p - 1) (2 - 1) ≤ 2 * (p - 1) := by omega
      _ ≤ p * 2 := by omega
  have hpo : Odd p := hp.odd_of_ne_two hp2'
  have hqo : Odd q := hq.odd_of_ne_two hq2'
  have hpe : 2 ∣ p - 1 := by
    obtain ⟨k, hk⟩ := hpo; exact ⟨k, by omega⟩
  have hqe : 2 ∣ q - 1 := by
    obtain ⟨k, hk⟩ := hqo; exact ⟨k, by omega⟩
  have hg : 2 ≤ Nat.gcd (p - 1) (q - 1) :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by omega)) (Nat.dvd_gcd hpe hqe)
  have hgl := Nat.gcd_mul_lcm (p - 1) (q - 1)
  have hle : (p - 1) * (q - 1) ≤ p * q := Nat.mul_le_mul (by omega) (by omega)
  nlinarith

/-- The period of a unit modulo a product of two distinct primes is at most half the modulus. -/
theorem two_period_le (p q N m : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hN : N = p * q) (hcop : Nat.Coprime m N) :
    2 * orderOf (m : ZMod N) ≤ N := by
  set k := Nat.lcm (p - 1) (q - 1) with hk
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hkpos : 0 < k := Nat.lcm_pos (by omega) (by omega)
  have hmp : Nat.Coprime m p := Nat.Coprime.coprime_dvd_right (by rw [hN]; exact Nat.dvd_mul_right _ _) hcop
  have hmq : Nat.Coprime m q := Nat.Coprime.coprime_dvd_right (by rw [hN]; exact Nat.dvd_mul_left _ _) hcop
  have h1 : m ^ k ≡ 1 [MOD p] := by
    have hf := Nat.ModEq.pow_totient hmp
    rw [Nat.totient_prime hp] at hf
    obtain ⟨t, ht⟩ : p - 1 ∣ k := Nat.dvd_lcm_left _ _
    rw [ht, pow_mul]
    simpa using hf.pow t
  have h2 : m ^ k ≡ 1 [MOD q] := by
    have hf := Nat.ModEq.pow_totient hmq
    rw [Nat.totient_prime hq] at hf
    obtain ⟨t, ht⟩ : q - 1 ∣ k := Nat.dvd_lcm_right _ _
    rw [ht, pow_mul]
    simpa using hf.pow t
  have hpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have h3 : m ^ k ≡ 1 [MOD N] := by
    rw [hN]; exact (Nat.modEq_and_modEq_iff_modEq_mul hpq).mp ⟨h1, h2⟩
  have h4 : (m : ZMod N) ^ k = 1 := by
    have := (ZMod.natCast_eq_natCast_iff (m ^ k) 1 N).mpr h3
    simpa using this
  have h5 : orderOf (m : ZMod N) ≤ k := Nat.le_of_dvd hkpos (orderOf_dvd_of_pow_eq_one h4)
  have h6 : 2 * k ≤ N := by rw [hN, hk]; exact two_lcm_le p q hp hq hne
  omega

end FowlerLSQC.ShorAux

open FowlerLSQC.ShorAux in
open FowlerLSQC.Shor in
theorem solution (N₁ N₂ N m c j : ℕ) (hN₁ : N₁.Prime) (hN₂ : N₂.Prime) (hne : N₁ ≠ N₂)
    (hN : N = N₁ * N₂) (hm1 : 1 < m) (hmN : m < N) (hcop : Nat.Coprime m N)
    (hc0 : 0 < c) (hcr : c < period N m)
    (hj : j = ⌊((c * 2 ^ (2 * binaryLength N) : ℕ) : ℚ) / (period N m : ℚ)⌋₊ ∨
      j = ⌈((c * 2 ^ (2 * binaryLength N) : ℕ) : ℚ) / (period N m : ℚ)⌉₊) :
    ∃ n : ℕ, ((j : ℝ) / 2 ^ (2 * binaryLength N)).convergent n = (c : ℚ) / (period N m : ℚ) := by
  set r := period N m with hr
  set L := binaryLength N with hL
  have hr2 : 2 * r ≤ N := two_period_le N₁ N₂ N m hN₁ hN₂ hne hN hcop
  have hNL : N < 2 ^ L := Nat.lt_size_self N
  have hrpos : 0 < r := by omega
  set q : ℚ := (c : ℚ) / (r : ℚ) with hq
  -- denominator bound
  have hden : q.den ≤ r := by
    have heq : q = Rat.divInt (c : ℤ) (r : ℤ) := by
      rw [Rat.divInt_eq_div]; push_cast; rfl
    have hd := Rat.den_dvd (c : ℤ) (r : ℤ)
    rw [← heq] at hd
    exact Nat.le_of_dvd hrpos (Int.natCast_dvd_natCast.mp hd)
  -- the key nat inequality 2 den^2 < 2^(2L)
  have hkey : 2 * q.den ^ 2 < 2 ^ (2 * L) := by
    have h1 : 2 * r < 2 ^ L := lt_of_le_of_lt hr2 hNL
    have h2 : q.den ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hden 2
    have h3 : (2 * r) ^ 2 < (2 ^ L) ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
    have h4 : (2 ^ L) ^ 2 = 2 ^ (2 * L) := by rw [← pow_mul, mul_comm]
    rw [h4] at h3
    have h5 : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
    omega
  -- |j - y| < 1 where y = c 2^(2L) / r
  set y : ℚ := ((c * 2 ^ (2 * L) : ℕ) : ℚ) / (r : ℚ) with hy
  have hy0 : 0 ≤ y := by positivity
  have hjy : |(j : ℚ) - y| < 1 := by
    rcases hj with hj | hj
    · have a1 : (j : ℚ) ≤ y := by rw [hj]; exact Nat.floor_le hy0
      have a2 : y < (j : ℚ) + 1 := by rw [hj]; exact Nat.lt_floor_add_one y
      rw [abs_lt]; constructor <;> linarith
    · have a1 : y ≤ (j : ℚ) := by rw [hj]; exact Nat.le_ceil y
      have a2 : (j : ℚ) < y + 1 := by rw [hj]; exact Nat.ceil_lt_add_one hy0
      rw [abs_lt]; constructor <;> linarith
  have hD : (0 : ℝ) < 2 ^ (2 * L) := by positivity
  have hjyR : |(j : ℝ) - (y : ℝ)| < 1 := by
    have := hjy
    rw [← Rat.cast_lt (K := ℝ)] at this
    push_cast at this ⊢
    exact this
  have hyR : (y : ℝ) = (c : ℝ) * 2 ^ (2 * L) / (r : ℝ) := by
    rw [hy]; push_cast; ring
  have hqR : ((q : ℚ) : ℝ) = (c : ℝ) / (r : ℝ) := by
    rw [hq]; push_cast; ring
  have happrox : |(j : ℝ) / 2 ^ (2 * L) - (q : ℝ)| < 1 / (2 * (q.den : ℝ) ^ 2) := by
    have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
    have e : (j : ℝ) / 2 ^ (2 * L) - (q : ℝ) = ((j : ℝ) - (y : ℝ)) / 2 ^ (2 * L) := by
      rw [hyR, hqR]; field_simp
    rw [e, abs_div, abs_of_pos hD, div_lt_iff₀ hD]
    have hkR : (2 * (q.den : ℝ) ^ 2) < 2 ^ (2 * L) := by exact_mod_cast hkey
    have hdpos : (0 : ℝ) < 2 * (q.den : ℝ) ^ 2 := by
      have : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
      positivity
    have : 1 < 1 / (2 * (q.den : ℝ) ^ 2) * 2 ^ (2 * L) := by
      rw [one_div, inv_mul_eq_div, one_lt_div hdpos]; exact hkR
    linarith
  obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent happrox
  exact ⟨n, hn.symm⟩
