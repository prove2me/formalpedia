-- Prove2me | solution 1 for GNFS.nontrivial_gcd_of_sq_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:47:49.093499+00:00
-- url     : https://prove2.me/submissions/1b554609-ecbd-4c6a-969b-571f2328dcfc

import Mathlib
import Definitions.Def_GNFS_defs

theorem solution (n : ℕ) (x y : ℤ) (h : (n : ℤ) ∣ x ^ 2 - y ^ 2)
    (hsub : ¬ (n : ℤ) ∣ x - y) (hadd : ¬ (n : ℤ) ∣ x + y) :
    1 < Int.gcd (x - y) n ∧ Int.gcd (x - y) n < n := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, zero_dvd_iff] at h hsub hadd
    have : (x - y) * (x + y) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hsub h1
    · exact hadd h1
  have hprod : (n : ℤ) ∣ (x - y) * (x + y) := by
    have : (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
    rw [this]; exact h
  have hg0 : 0 < Int.gcd (x - y) n := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hn0)
  have hgd : (Int.gcd (x - y) n : ℤ) ∣ n := Int.gcd_dvd_right _ _
  have hgle : Int.gcd (x - y) n ≤ n := by
    have := Int.le_of_dvd (by exact_mod_cast Nat.pos_of_ne_zero hn0) hgd
    exact_mod_cast this
  constructor
  · by_contra hc
    have h1 : Int.gcd (x - y) n = 1 := by omega
    have hcop : IsCoprime (n : ℤ) (x - y) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact h1
    exact hadd (hcop.dvd_of_dvd_mul_left hprod)
  · by_contra hc
    have h1 : Int.gcd (x - y) n = n := by omega
    have : ((Int.gcd (x - y) n : ℕ) : ℤ) ∣ x - y := Int.gcd_dvd_left _ _
    rw [h1] at this
    exact hsub this
