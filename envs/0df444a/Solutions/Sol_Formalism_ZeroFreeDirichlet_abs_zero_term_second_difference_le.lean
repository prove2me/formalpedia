-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.abs_zero_term_second_difference_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:43:15.947817+00:00
-- url     : https://prove2.me/submissions/5ab33171-c50c-47f5-a73f-cb0cd8c1f8fa

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_AbsZeroTermSecondDifferenceLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.ZeroFreeDirichlet
private theorem one_add_rpow_le_one_add_mul {s p : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 + s) ^ p ≤ 1 + p * s := by
  have t := Real.geom_mean_le_arith_mean2_weighted hp0 (sub_nonneg.2 hp1)
    (by linarith : (0:ℝ) ≤ 1 + s) zero_le_one (by ring : p + (1 - p) = 1)
  rw [Real.one_rpow, mul_one] at t
  nlinarith [t]
end Formalism.ZeroFreeDirichlet
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {y h β : ℝ} (hy : 1 ≤ y) (hh : 0 < h) (_hh1 : h ≤ 1) (hβ1 : 1 / 2 ≤ β)
    (hβ2 : β < 1) :
    |(y * (1 + h)) * (y ^ β / (β * (β - 1))) - y * ((y * (1 + h)) ^ β / (β * (β - 1)))
        + y * h * (y ^ β / β)| ≤ 2 * y ^ 2 * h ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have h1 : (0:ℝ) < 1 + h := by linarith
  have hβ0 : 0 < β := by linarith
  have hq : 0 < 1 - β := by linarith
  have hβne : β ≠ 0 := hβ0.ne'
  have hβ1ne : β - 1 ≠ 0 := by linarith
  have hq1ne : 1 - β ≠ 0 := hq.ne'
  have hmul : (y * (1 + h)) ^ β = y ^ β * (1 + h) ^ β := Real.mul_rpow hy0 h1.le
  have hAq : (1 + h) ^ β * (1 + h) ^ (1 - β) = 1 + h := by
    have e : β + (1 - β) = 1 := by ring
    rw [← Real.rpow_add h1, e, Real.rpow_one]
  have hBern : (1 + h) ^ (1 - β) ≤ 1 + (1 - β) * h :=
    one_add_rpow_le_one_add_mul hh.le hq.le (by linarith)
  have hD0 : (1 + h) ^ β ≤ 1 + β * h := one_add_rpow_le_one_add_mul hh.le hβ0.le hβ2.le
  have hA0 : 0 ≤ (1 + h) ^ β := Real.rpow_nonneg h1.le _
  have hB0 : 0 ≤ y ^ β := Real.rpow_nonneg hy0 _
  have hBy : y ^ β ≤ y := by
    have t := Real.rpow_le_rpow_of_exponent_le hy hβ2.le
    rwa [Real.rpow_one] at t
  set A := (1 + h) ^ β with hA
  set B := y ^ β with hB
  have hD1 : (1 + β * h - A) * (1 + (1 - β) * h) ≤ β * (1 - β) * h ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hBern hA0]
  have hD2 : 1 + β * h - A ≤ β * (1 - β) * h ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hD0) (mul_nonneg hq.le hh.le)]
  have key : (y * (1 + h)) * (B / (β * (β - 1))) - y * ((y * (1 + h)) ^ β / (β * (β - 1)))
      + y * h * (B / β) = -(y * B * ((1 + β * h - A) / (β * (1 - β)))) := by
    rw [hmul]
    field_simp
    ring
  rw [key, abs_neg]
  have hpos : 0 < β * (1 - β) := mul_pos hβ0 hq
  have hE0 : 0 ≤ (1 + β * h - A) / (β * (1 - β)) := div_nonneg (by linarith) hpos.le
  have hE : (1 + β * h - A) / (β * (1 - β)) ≤ h ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hy0 hB0) hE0)]
  have s1 : y * B * ((1 + β * h - A) / (β * (1 - β))) ≤ y * B * h ^ 2 :=
    mul_le_mul_of_nonneg_left hE (mul_nonneg hy0 hB0)
  have s2 : y * B * h ^ 2 ≤ y * y * h ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBy hy0) (sq_nonneg h)
  nlinarith [mul_nonneg (sq_nonneg y) (sq_nonneg h)]
end Formalism.ZeroFreeDirichlet
