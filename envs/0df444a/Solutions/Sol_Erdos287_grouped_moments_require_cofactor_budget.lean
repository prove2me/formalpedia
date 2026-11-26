-- Prove2me | solution 1 for Erdos287.grouped_moments_require_cofactor_budget
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:34:15.20237+00:00
-- url     : https://prove2.me/submissions/1407fe86-9db4-48dd-a029-0cd436d35ed7

import Mathlib

set_option autoImplicit false

/-- The grouped moment inequalities and the affine neighbor capacity
force a large cofactor budget even with edge-only compatibility. -/
theorem solution (N B T σ r A μ : ℝ)
    (hN : 11 ≤ N) (hB : 0 ≤ B) (hT : 0 ≤ T ∧ T ≤ 2 * B * N)
    (hσ : 0 ≤ σ ∧ σ ≤ 1 / 4) (hA : 18 / 5 ≤ A) (hAr : A < r)
    (hr : r ≤ 93 / 25) (hmean : N * μ ≤ 2 * σ * Real.log (1 + T))
    (hsieve : 1 - A * σ < μ * (r - A)) :
    (55 / 3 : ℝ) < Real.log (1 + 22 * B) := by
  have hNp : 0 < N := by linarith
  have hAp : 0 ≤ A := by linarith
  have hμ : (5 / 6 : ℝ) < μ := by
    by_contra! hbad
    have hleft := mul_le_mul_of_nonneg_right hbad (sub_nonneg.mpr hAr.le)
    have hright := mul_le_mul_of_nonneg_left hσ.2 hAp
    nlinarith only [hleft, hright, hA, hr, hsieve]
  have hlog : Real.log (1 + T) ≤ Real.log (1 + 2 * B * N) :=
    Real.log_le_log (by linarith [hT.1]) (by linarith [hT.2])
  have hlog0 : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith [hT.1])
  have hscaled := mul_le_mul_of_nonneg_right (show 2 * σ ≤ 1 / 2 by linarith [hσ.2]) hlog0
  have hstrict := mul_lt_mul_of_pos_left hμ hNp
  have hbig : (5 / 3 : ℝ) * N < Real.log (1 + 2 * B * N) := by
    nlinarith only [hscaled, hmean, hstrict, hlog]
  let w : ℝ := 11 / N
  have hw : 0 < w := div_pos (by norm_num) hNp
  have hw1 : w ≤ 1 := (div_le_iff₀ hNp).mpr (by simpa using hN)
  have hwN : w * N = 11 := div_mul_cancel₀ _ hNp.ne'
  have hpositive : 1 + 2 * B * N ∈ Set.Ioi (0 : ℝ) := by
    change 0 < 1 + 2 * B * N
    positivity
  have hcon := strictConcaveOn_log_Ioi.concaveOn.2
    hpositive (show (1 : ℝ) ∈ Set.Ioi (0 : ℝ) by change (0 : ℝ) < 1; norm_num)
    hw.le (sub_nonneg.mpr hw1) (show w + (1 - w) = 1 by ring)
  rw [smul_eq_mul, smul_eq_mul, Real.log_one, mul_zero, add_zero,
    smul_eq_mul, smul_eq_mul, mul_one] at hcon
  have heq : w * (1 + 2 * B * N) + (1 - w) = 1 + 22 * B := by
    linear_combination (2 * B) * hwN
  rw [heq] at hcon
  have hfinal := mul_lt_mul_of_pos_left hbig hw
  calc
    (55 / 3 : ℝ) = w * ((5 / 3) * N) := by rw [← mul_left_comm, hwN]; norm_num
    _ < _ := hfinal.trans_le hcon

