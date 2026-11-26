-- Prove2me | solution 1 for Erdos287.proth_prime_certificate
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T09:34:58.192485+00:00
-- url     : https://prove2.me/submissions/573f2c96-a084-4ac6-9216-aef01236caa2

import Mathlib

set_option autoImplicit false

/-- A single modular power certifies primality for a Proth number. -/
theorem solution (k e g : ℕ) (hk : 0 < k) (hsmall : k < 2 ^ (e + 1))
    (hg : (g : ZMod (k * 2 ^ (e + 1) + 1)) ^ (k * 2 ^ e) = -1) :
    (k * 2 ^ (e + 1) + 1).Prime := by
  let n := k * 2 ^ (e + 1) + 1
  change n.Prime
  change (g : ZMod n) ^ (k * 2 ^ e) = -1 at hg
  have hpos : 0 < k * 2 ^ (e + 1) := Nat.mul_pos hk (by positivity)
  have hn : 1 < n := by dsimp [n]; omega
  by_contra hnp
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hn2 : n = 2 * (k * 2 ^ e) + 1 := by
    dsimp [n]
    rw [pow_succ]
    ring
  have hpgt : 2 < p := by
    have hple := hp.two_le
    by_contra! h
    have hp2 : p = 2 := by omega
    rw [hp2, hn2] at hpn
    omega
  let _ : Fact (2 < p) := ⟨hpgt⟩
  let _ : Fact p.Prime := ⟨hp⟩
  let φ := ZMod.castHom hpn (ZMod p)
  let z := (g : ZMod p) ^ k
  have hcast : (g : ZMod p) ^ (k * 2 ^ e) = -1 := calc
    _ = φ ((g : ZMod n) ^ (k * 2 ^ e)) := by rw [map_pow, map_natCast]
    _ = φ (-1) := congrArg φ hg
    _ = _ := by rw [map_neg, map_one]
  have hz : z ^ 2 ^ e = -1 := by simpa [z, pow_mul] using hcast
  have hzne : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by positivity)] at hz
    exact neg_ne_zero.mpr one_ne_zero hz.symm
  have hzfull : z ^ 2 ^ (e + 1) = 1 := by
    rw [pow_succ, pow_mul, hz]
    norm_num
  have horder : orderOf z = 2 ^ (e + 1) := by
    apply Nat.eq_prime_pow_of_dvd_least_prime_pow Nat.prime_two
    · intro h
      exact ZMod.neg_one_ne_one (hz.symm.trans (orderOf_dvd_iff_pow_eq_one.mp h))
    · exact orderOf_dvd_iff_pow_eq_one.mpr hzfull
  have hdiv : 2 ^ (e + 1) ∣ p - 1 := by
    rw [← horder]
    exact orderOf_dvd_iff_pow_eq_one.mpr (ZMod.pow_card_sub_one_eq_one hzne)
  have hle : 2 ^ (e + 1) ≤ p - 1 := Nat.le_of_dvd (by omega) hdiv
  have hsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  dsimp [n] at hsq
  have hpowpos : 0 < (2 : ℕ) ^ (e + 1) := by positivity
  have hb : 2 ^ (e + 1) + 1 ≤ p := by omega
  have hbpow := Nat.pow_le_pow_left hb 2
  have hmul := Nat.mul_lt_mul_of_pos_right hsmall hpowpos
  nlinarith only [hbpow, hmul, hpowpos, hsq]

