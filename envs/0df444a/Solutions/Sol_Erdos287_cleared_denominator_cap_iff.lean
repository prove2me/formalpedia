-- Prove2me | solution 1 for Erdos287.cleared_denominator_cap_iff
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:37:35.818176+00:00
-- url     : https://prove2.me/submissions/89b8c35c-7a4c-4613-a070-568e7e920d88

import Mathlib

set_option autoImplicit false

/-- A cap on the reduced denominator is equivalent to divisibility of the
cleared numerator by the part of the clearing denominator outside the cap. -/
theorem solution (W L C : ℕ) (hL : 0 < L) :
    ((W : ℚ) / L).den ∣ C ↔ L / L.gcd C ∣ W := by
  have hrat : ((W : ℚ) / L).den = L / L.gcd W := by
    rw [show (W : ℚ) / L = Rat.divInt (W : ℤ) (L : ℤ) by
      rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast], Rat.divInt_ofNat, Rat.den_mkRat]
    simp [hL.ne']
  have hdvd (x y : ℕ) : L / L.gcd x ∣ y ↔ L ∣ y * x := by
    rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left L x) (Nat.gcd_pos_of_pos_left x hL)]
    rw [mul_comm (L.gcd x) y]
    exact Nat.dvd_mul_gcd_iff_dvd_mul
  rw [hrat, hdvd, hdvd, Nat.mul_comm C W]

