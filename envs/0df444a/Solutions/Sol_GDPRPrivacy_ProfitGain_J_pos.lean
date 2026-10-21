-- Prove2me | solution 1 for GDPRPrivacy.ProfitGain.J_pos
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:41:52.025005+00:00
-- url     : https://prove2.me/submissions/98d69014-500b-4db7-9ee3-02dc782f21be

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model
set_option autoImplicit false


theorem solution (x α : ℝ) (hx0 : 0 < x) (hxhalf : x < 1 / 2) (hα : 0 ≤ α)
    (hα1 : α < (1 - 2 * x) / 2) :
    0 < 76 + 27 * x ^ 4 - 96 * α - 32 * α ^ 2 * (3 + α) + 12 * x ^ 2 * (1 + α) * (1 + 9 * α)
      - (4 * x ^ 3 * (8 + 27 * α) + 24 * x * (4 + 4 * α ^ 2 - α)) := by
  obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = (1 - 2 * x) / 2 - α := ⟨_, rfl⟩
  have hd : 0 < d := by rw [hdd]; linarith
  have e : 76 + 27 * x ^ 4 - 96 * α - 32 * α ^ 2 * (3 + α) + 12 * x ^ 2 * (1 + α) * (1 + 9 * α)
      - (4 * x ^ 3 * (8 + 27 * α) + 24 * x * (4 + 4 * α ^ 2 - α)) =
      1728 * α ^ 3 * d + 864 * α ^ 3 * x + 4608 * α ^ 2 * d ^ 2 + 6912 * α ^ 2 * d * x + 2700 * α ^ 2 * x ^ 2 + 4096 * α * d ^ 3 + 10080 * α * d ^ 2 * x + 8208 * α * d * x ^ 2 + 2052 * α * x ^ 3 + 1216 * d ^ 4 + 4096 * d ^ 3 * x + 5040 * d ^ 2 * x ^ 2 + 2592 * d * x ^ 3 + 459 * x ^ 4 := by
    rw [hdd]; ring
  rw [e]; positivity
