-- Prove2me | solution 1 for Erdos77.binomial_mean_mass_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T20:55:08.073685+00:00
-- url     : https://prove2.me/submissions/31b98fc7-a01d-4fcd-9a34-e56db3d0b82a

import Mathlib
import Theorems.Thm_Erdos77_binomial_entropy_integer_form

open Erdos77

/-- The mode of the binomial distribution at `r` carries mass at least
`1 / (n + 1)`.  This is the Proved multiplicative integer bound divided by the
positive quantity `(n + 1) * n ^ n`. -/
theorem solution (n r : Nat) (hr : 0 < r) (hrn : r < n) :
    (1 : Real) / ((n + 1 : Nat) : Real) <=
      (Nat.choose n r : Real) * ((r : Real) / (n : Real)) ^ r *
        ((Nat.cast (n - r) : Real) / (n : Real)) ^ (n - r) := by
  have hcore := Erdos77.binomial_entropy_integer_form n r hr hrn
  have hn0 : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hrn)
  have hn1 : (0 : Real) < ((n + 1 : Nat) : Real) := by
    exact_mod_cast Nat.succ_pos n
  have hmerge : (n : Real) ^ r * (n : Real) ^ (n - r) = (n : Real) ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hrn.le]
  have hnorm : (Nat.choose n r : Real) * ((r : Real) / (n : Real)) ^ r *
        ((Nat.cast (n - r) : Real) / (n : Real)) ^ (n - r)
      = (Nat.choose n r : Real) * (r : Real) ^ r *
          (Nat.cast (n - r) : Real) ^ (n - r) / (n : Real) ^ n := by
    rw [div_pow, div_pow, ← hmerge]
    ring
  rw [hnorm, le_div_iff₀ (pow_pos hn0 _), div_mul_eq_mul_div, one_mul,
    div_le_iff₀ hn1]
  have hreorder : (Nat.choose n r : Real) * (r : Real) ^ r *
        (Nat.cast (n - r) : Real) ^ (n - r) * ((n + 1 : Nat) : Real)
      = ((n + 1 : Nat) : Real) * (Nat.choose n r : Real) * (r : Real) ^ r *
        (Nat.cast (n - r) : Real) ^ (n - r) := by ring
  rw [hreorder]
  exact hcore
