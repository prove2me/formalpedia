-- Prove2me | solution 2 for CohnElkies.saddleSmallResidue_tail_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:36:17.932331+00:00
-- url     : https://prove2.me/submissions/5d4676c3-0703-470c-b1d3-6ff1c49b7cb5

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {C ℓ y : ℝ}
    (hy : 0 ≤ y)
    (hyupper : y ≤ Real.log ℓ / 8 + C) :
    Real.exp y *
        (y ^ (saddleSmallResidueTruncation ℓ + 1) /
          ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ)) ≤
      saddleSmallResidueTailMajorant C ℓ := by
  unfold saddleSmallResidueTailMajorant
  have hs : 0 ≤ Real.log ℓ / 8 + C := hy.trans hyupper
  have hN : 20 * Real.log ℓ ≤ (saddleSmallResidueTruncation ℓ : ℝ) := Nat.le_ceil _
  have hfac : 0 < ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ) := by positivity
  have hA : y ^ (saddleSmallResidueTruncation ℓ + 1) ≤
      (Real.log ℓ / 8 + C) ^ (saddleSmallResidueTruncation ℓ + 1) :=
    pow_le_pow_left₀ hy hyupper _
  have hB : (2 * (Real.log ℓ / 8 + C)) ^ (saddleSmallResidueTruncation ℓ + 1) /
      ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ) ≤
      Real.exp (2 * (Real.log ℓ / 8 + C)) :=
    Real.pow_div_factorial_le_exp _ (by positivity) _
  have hC : Real.exp (10 * Real.log ℓ) ≤ (2 : ℝ) ^ (saddleSmallResidueTruncation ℓ + 1) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 2), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have := Real.log_two_gt_d9
    push_cast
    rcases le_total 0 (Real.log ℓ) with h | h <;> nlinarith
  calc Real.exp y * (y ^ (saddleSmallResidueTruncation ℓ + 1) /
          ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ))
      ≤ Real.exp (Real.log ℓ / 8 + C) * ((Real.log ℓ / 8 + C) ^ (saddleSmallResidueTruncation ℓ + 1) /
          ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ)) :=
        mul_le_mul (Real.exp_le_exp.mpr hyupper) (div_le_div_of_nonneg_right hA hfac.le)
          (by positivity) (by positivity)
    _ = Real.exp (Real.log ℓ / 8 + C) * ((2 * (Real.log ℓ / 8 + C)) ^ (saddleSmallResidueTruncation ℓ + 1) /
          ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ)) / (2 : ℝ) ^ (saddleSmallResidueTruncation ℓ + 1) := by
        rw [mul_pow]; field_simp
    _ ≤ Real.exp (Real.log ℓ / 8 + C) * Real.exp (2 * (Real.log ℓ / 8 + C)) / Real.exp (10 * Real.log ℓ) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hB (by positivity)) (by positivity) hC
    _ = Real.exp (3 * C - (77 / 8 : ℝ) * Real.log ℓ) := by
        rw [← Real.exp_add, ← Real.exp_sub]; congr 1; ring

