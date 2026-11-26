-- Prove2me | solution 1 for Erdos287.prime_of_lucas_two_factors
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T05:02:11.465263+00:00
-- url     : https://prove2.me/submissions/bc56408f-43e1-444d-8388-dfee878d58d3

import Mathlib

set_option autoImplicit false

/-- A Lucas certificate for a prime candidate whose predecessor has no
prime factors other than two and a supplied prime. -/
theorem solution (n p a g : ℕ) (hp : p.Prime) (hfactor : n - 1 = p * 2 ^ a)
    (hfull : (g : ZMod n) ^ (n - 1) = 1)
    (htwo : (g : ZMod n) ^ ((n - 1) / 2) ≠ 1)
    (hprime : (g : ZMod n) ^ ((n - 1) / p) ≠ 1) :
    n.Prime := by
  apply lucas_primality n (g : ZMod n) hfull
  intro r hr hdiv
  rw [hfactor] at hdiv
  rcases (Nat.Prime.dvd_mul hr).mp hdiv with h | h
  · have he : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp h
    simpa only [he] using hprime
  · have hd : r ∣ 2 := hr.dvd_of_dvd_pow h
    have he : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hd
    simpa only [he] using htwo

