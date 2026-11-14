-- Prove2me | solution 1 for ConsistentSubmodular.middle_sign_u_H
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:44.594785+00:00
-- url     : https://prove2.me/submissions/72cc52fa-ee37-4b27-b6e6-b4ea2ae6ab33

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

theorem solution (k : ℝ) (hl : (38 / 23 : ℝ) ≤ k) (hu : k ≤ (7 / 4 : ℝ)) :
    0 < k ^ 3 + 4 * k ^ 2 - 51 * k + 72 := by
  let t := (k - (38 / 23 : ℝ)) / (9 / 92 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : k ^ 3 + 4 * k ^ 2 - 51 * k + 72 =
      (38542 / 12167 : ℝ) * (1 - t) ^ 3 +
      3 * (4661 / 2116 : ℝ) * t * (1 - t) ^ 2 +
      3 * (233 / 184 : ℝ) * t ^ 2 * (1 - t) +
      (23 / 64 : ℝ) * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (38542 / 12167 : ℝ) (4661 / 2116 : ℝ) (233 / 184 : ℝ) (23 / 64 : ℝ) ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end
