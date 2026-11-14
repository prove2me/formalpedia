-- Prove2me | solution 1 for ConsistentSubmodular.middle_sign_u_F2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:27:52.231261+00:00
-- url     : https://prove2.me/submissions/684ac99a-5caa-4731-a64f-4c1fd4f54fe2

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
    0 < k ^ 3 + 39 * k ^ 2 - 153 * k + 144 := by
  let t := (k - (7 / 4 : ℝ)) / (1 / 4 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : k ^ 3 + 39 * k ^ 2 - 153 * k + 144 =
      (67 / 64 : ℝ) * (1 - t) ^ 3 +
      3 * (7 / 16 : ℝ) * t * (1 - t) ^ 2 +
      3 * (3 / 4 : ℝ) * t ^ 2 * (1 - t) +
      2 * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (67 / 64 : ℝ) (7 / 16 : ℝ) (3 / 4 : ℝ) 2 ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end
