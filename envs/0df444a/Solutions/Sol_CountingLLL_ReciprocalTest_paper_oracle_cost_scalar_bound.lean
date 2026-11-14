-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.paper_oracle_cost_scalar_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:17:44.717295+00:00
-- url     : https://prove2.me/submissions/80510191-f19f-4bf8-a806-c949c75e36c4

import Mathlib
set_option autoImplicit false

theorem solution (u M : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 33/80)
    (hM0 : 0 ≤ M) (hM : M ≤ 74/25) :
    1-u+(1-u^2)/(1-u+u^2) * (1-u+u/(1-u+u^2)*M) < 3 := by
  let d : ℝ := 1-u+u^2
  let t : ℝ := 33/80-u
  have hd : 0 < d := by dsimp [d]; nlinarith [sq_nonneg u]
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 33/80 := by dsimp [t]; linarith
  have hu2 : u^2 ≤ 1 := by nlinarith [sq_nonneg (u+(33/80:ℝ))]
  have hcoef : 0 ≤ ((1-u^2)/d)*(u/d) := by positivity
  have hcomp : ((1-u^2)/d)*(u/d)*M ≤ ((1-u^2)/d)*(u/d)*(74/25) :=
    mul_le_mul_of_nonneg_left hM hcoef
  have hpoly : (3-(1-u+(1-u^2)/d*(1-u+u/d*(74/25))))*d^2 =
      (231109/102400000:ℝ) + (138699/320000)*t +
        ((49839/8000)-(213/50)*t)*t^2 + 2*t^4 := by
    have hdn : 1-u+u^2 ≠ 0 := by simpa [d] using (ne_of_gt hd)
    dsimp [d,t]
    field_simp [hdn]
    <;> ring
  have hq : 0 ≤ ((49839/8000:ℝ)-(213/50)*t)*t^2 :=
    mul_nonneg (by nlinarith) (sq_nonneg t)
  have hpolypos : 0 < (3-(1-u+(1-u^2)/d*(1-u+u/d*(74/25))))*d^2 := by
    rw [hpoly]
    positivity
  have hbase : 1-u+(1-u^2)/d*(1-u+u/d*(74/25)) < 3 := by
    nlinarith [sq_pos_of_pos hd]
  change 1-u+(1-u^2)/d*(1-u+u/d*M) < 3
  nlinarith
