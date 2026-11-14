-- Prove2me | solution 1 for ConsistentSubmodular.middle_sign_u_G1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:27:25.768503+00:00
-- url     : https://prove2.me/submissions/e7389015-4564-44ce-8977-7c81760fa1c2

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

theorem solution (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < -3 * k ^ 3 - 42 * k ^ 2 + 319 * k - 360 := by
  let t := (k - (7 / 4 : ℝ)) / (1 / 4 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : -3 * k ^ 3 - 42 * k ^ 2 + 319 * k - 360 =
      (3427 / 64 : ℝ) * (1 - t) ^ 3 +
      3 * (787 / 12 : ℝ) * t * (1 - t) ^ 2 +
      3 * (917 / 12 : ℝ) * t ^ 2 * (1 - t) +
      86 * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (3427 / 64 : ℝ) (787 / 12 : ℝ) (917 / 12 : ℝ) 86 ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end
