-- Prove2me | solution 1 for FractionalCalc.mittagLeffler_two_cos
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-22T02:06:23.660696+00:00
-- url     : https://prove2.me/submissions/6b77c57e-0cc5-43e7-833c-b410f9739d84

import Definitions.Def_FractionalCalc_mittagLeffler

open FractionalCalc

/-- The order-two Mittag-Leffler series is the cosine series. -/
theorem solution (z : ℝ) : mittagLefflerOne 2 (-(z ^ 2)) = Real.cos z := by
  unfold mittagLefflerOne mittagLeffler
  rw [Real.cos_eq_tsum]
  apply tsum_congr
  intro k
  have hgamma : Real.Gamma (2 * (k : ℝ) + 1) = ((2 * k).factorial : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using Real.Gamma_nat_eq_factorial (2 * k)
  rw [hgamma]
  congr 1
  rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul]
