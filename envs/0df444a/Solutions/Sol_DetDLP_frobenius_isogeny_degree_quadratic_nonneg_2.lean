-- Prove2me | solution 2 for DetDLP.frobenius_isogeny_degree_quadratic_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T16:41:10.015864+00:00
-- url     : https://prove2.me/submissions/1f12a00a-92e8-4457-9684-989f57aefc48

import Theorems.Thm_DetDLP_hasse_ec_point_count_bound

set_option autoImplicit false
open DetDLP

theorem solution :
    ∀ (p : ℕ) [Fact p.Prime], 3 < p →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let N := Fintype.card E.toAffine.Point
        ∀ m n : ℤ, 0 ≤ m ^ 2 * (p : ℤ) - m * n * ((p : ℤ) + 1 - (N : ℤ)) + n ^ 2 := by
  intro p hp h3 E hE
  letI := ecPointFintype E
  let N := Fintype.card E.toAffine.Point
  let t : ℤ := (p : ℤ) + 1 - N
  have habs : |(N : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ) :=
    hasse_ec_point_count_bound p h3 E
  have hsq := mul_self_le_mul_self (abs_nonneg _) habs
  rw [← sq, sq_abs] at hsq
  have hreal : ((p : ℝ) + 1 - N) ^ 2 ≤ 4 * p := by
    nlinarith only [hsq, Real.sq_sqrt (Nat.cast_nonneg p)]
  have hdisc : 0 ≤ 4 * (p : ℤ) - t ^ 2 := by
    apply sub_nonneg.mpr
    dsimp [t]
    exact_mod_cast hreal
  change ∀ m n : ℤ, 0 ≤ m ^ 2 * (p : ℤ) - m * n * t + n ^ 2
  intro m n
  change 0 ≤ m ^ 2 * (p : ℤ) - m * n * t + n ^ 2
  nlinarith only [mul_nonneg (sq_nonneg m) hdisc, sq_nonneg (2*n - m*t)]

#print axioms solution
