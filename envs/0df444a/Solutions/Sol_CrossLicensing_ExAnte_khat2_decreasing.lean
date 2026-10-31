-- Prove2me | solution 1 for CrossLicensing.ExAnte.khat2_decreasing
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:11:57.783413+00:00
-- url     : https://prove2.me/submissions/3d6ac185-5bf3-4c09-b5ff-341477a7df0e

import Mathlib
import Definitions.Def_CrossLicensing_ExAnte_Model
open CrossLicensing.ExAnte

theorem solution(k1 : ℝ) (hk1 : (49 : ℝ) / 144 < k1) :
    StrictAntiOn (fun β : ℝ => khat2 k1 β) (Set.Icc 0 1) ∧
      khat2 k1 1 = 0 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hlo : 3 / 2 < Real.sqrt 3 := by nlinarith
  have hhi : Real.sqrt 3 < 7 / 4 := by nlinarith
  have hk : 0 < k1 := by linarith
  constructor
  · intro a ha b hb hab
    obtain ⟨ha0, ha1⟩ := ha
    obtain ⟨hb0, hb1⟩ := hb
    simp only [khat2]
    set s := Real.sqrt 3 with hsdef
    have hua : 0 ≤ (a - 1) * (5 * a - 7) := by nlinarith
    have hub : 0 ≤ (b - 1) * (5 * b - 7) := by nlinarith
    have hu : (b - 1) * (5 * b - 7) < (a - 1) * (5 * a - 7) := by
      nlinarith [mul_pos (sub_pos.2 hab) (by linarith : (0:ℝ) < 12 - 5 * (a + b))]
    have hDa : (4 * s - 7) * (a - 1) * (5 * a - 7) + 48 * (3 - 2 * s) * k1 < 0 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 7 - 4 * s) hua,
        mul_pos (by linarith : (0:ℝ) < 2 * s - 3) hk]
    have hDb : (4 * s - 7) * (b - 1) * (5 * b - 7) + 48 * (3 - 2 * s) * k1 < 0 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 7 - 4 * s) hub,
        mul_pos (by linarith : (0:ℝ) < 2 * s - 3) hk]
    rw [← neg_div_neg_eq _ ((4 * s - 7) * (b - 1) * (5 * b - 7) + 48 * (3 - 2 * s) * k1),
      ← neg_div_neg_eq _ ((4 * s - 7) * (a - 1) * (5 * a - 7) + 48 * (3 - 2 * s) * k1),
      div_lt_div_iff₀ (by linarith) (by linarith)]
    have hc1 : 0 < 4 * s - 5 := by linarith
    have hc3 : 0 < 2 * s - 3 := by linarith
    nlinarith [mul_pos (mul_pos (mul_pos hc1 hc3) (mul_pos hk hk)) (sub_pos.2 hu)]
  · simp [khat2]
