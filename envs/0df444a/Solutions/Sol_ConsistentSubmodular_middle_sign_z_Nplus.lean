-- Prove2me | solution 1 for ConsistentSubmodular.middle_sign_z_Nplus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:15.695275+00:00
-- url     : https://prove2.me/submissions/e73b2a75-7117-4d4a-805d-814bf3996cf9

import Mathlib

section

namespace ConsistentSubmodular

private theorem cubic_positive (t c₀ c₁ c₂ c₃ : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (h₀ : 0 < c₀) (h₁ : 0 < c₁)
    (h₂ : 0 < c₂) (h₃ : 0 < c₃) :
    0 < c₀ * (1 - t) ^ 3 + 3 * c₁ * t * (1 - t) ^ 2 +
      3 * c₂ * t ^ 2 * (1 - t) + c₃ * t ^ 3 := by
  by_cases htlt : t < 1
  · have hs : 0 < 1 - t := sub_pos.mpr htlt
    positivity
  · have heq : t = 1 := by linarith
    simp [heq, h₃]

end ConsistentSubmodular

end

section

open ConsistentSubmodular

theorem solution (k : ℝ) (hl : (4 / 3 : ℝ) ≤ k) (hu : k ≤ (7 / 4 : ℝ)) :
    0 < 118 * k ^ 3 - 695 * k ^ 2 + 1081 * k - 378 := by
  let t := (k - (4 / 3 : ℝ)) / (5 / 12 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : 118 * k ^ 3 - 695 * k ^ 2 + 1081 * k - 378 =
      (2902 / 27 : ℝ) * (1 - t) ^ 3 +
      3 * (9463 / 108 : ℝ) * t * (1 - t) ^ 2 +
      3 * (2633 / 48 : ℝ) * t ^ 2 * (1 - t) +
      (567 / 32 : ℝ) * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (2902 / 27 : ℝ) (9463 / 108 : ℝ) (2633 / 48 : ℝ) (567 / 32 : ℝ) ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end
