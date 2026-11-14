-- Prove2me | solution 1 for ConsistentSubmodular.middle_sign_z_Nminus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:16.302754+00:00
-- url     : https://prove2.me/submissions/bf348b25-b32c-4e49-9e39-787e613da133

import Mathlib

section

namespace ConsistentSubmodular

private theorem quartic_positive (t c₀ c₁ c₂ c₃ c₄ : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (h₀ : 0 < c₀) (h₁ : 0 < c₁)
    (h₂ : 0 < c₂) (h₃ : 0 < c₃) (h₄ : 0 < c₄) :
    0 < c₀ * (1 - t) ^ 4 + 4 * c₁ * t * (1 - t) ^ 3 +
      6 * c₂ * t ^ 2 * (1 - t) ^ 2 + 4 * c₃ * t ^ 3 * (1 - t) + c₄ * t ^ 4 := by
  by_cases htlt : t < 1
  · have hs : 0 < 1 - t := sub_pos.mpr htlt
    positivity
  · have heq : t = 1 := by linarith
    simp [heq, h₄]

end ConsistentSubmodular

end

section

open ConsistentSubmodular

theorem solution (k : ℝ) (hl : (4 / 3 : ℝ) ≤ k) (hu : k ≤ (7 / 4 : ℝ)) :
    0 < -160 * k ^ 4 + 1196 * k ^ 3 - 2494 * k ^ 2 + 702 * k + 1512 := by
  let t := (k - (4 / 3 : ℝ)) / (5 / 12 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : -160 * k ^ 4 + 1196 * k ^ 3 - 2494 * k ^ 2 + 702 * k + 1512 =
      (27824 / 81 : ℝ) * (1 - t) ^ 4 +
      4 * (49739 / 216 : ℝ) * t * (1 - t) ^ 3 +
      6 * (57853 / 432 : ℝ) * t ^ 2 * (1 - t) ^ 2 +
      4 * (3881 / 64 : ℝ) * t ^ 3 * (1 - t) +
      (189 / 16 : ℝ) * t ^ 4 := by
    dsimp [t]
    ring
  rw [hid]
  exact quartic_positive t (27824 / 81 : ℝ) (49739 / 216 : ℝ) (57853 / 432 : ℝ) (3881 / 64 : ℝ) (189 / 16 : ℝ) ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end
