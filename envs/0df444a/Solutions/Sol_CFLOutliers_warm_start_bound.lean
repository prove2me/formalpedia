-- Prove2me | solution 1 for CFLOutliers.warm_start_bound
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T13:00:42.383203+00:00
-- url     : https://prove2.me/submissions/a767c2b9-139c-4a50-8cc0-cf2547007081

import Mathlib

set_option autoImplicit false

/-- The warm-start bound: constraint propagation gives `b ≤ H + t(1 - 3θ)`, and the two
regimes `θ ≤ 1/11` and `θ > 1/11` close the linear bound. -/
theorem solution (a b θ t H M : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ht : 0 ≤ t)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (ha : a ≤ H - 3 * θ * t) (hb : b ≤ a + t) :
    min b (a + θ * b + M) ≤ 12 / 11 * H + M := by
  by_cases hbX : b ≤ 12 / 11 * H + M
  · exact le_trans (min_le_left _ _) hbX
  · push_neg at hbX
    have hb_le : b ≤ H + t * (1 - 3 * θ) := by linarith
    have hHlt : H < 11 * t * (1 - 3 * θ) := by nlinarith
    have hkey : a + θ * b + M ≤ 12 / 11 * H + M := by
      have hbθ : θ * b ≤ θ * (H + t * (1 - 3 * θ)) :=
        mul_le_mul_of_nonneg_left hb_le (le_of_lt hθ0)
      by_cases hθ : θ ≤ 1 / 11
      · have h1 : (θ - 1 / 11) * H ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hH
        have h2 : 0 ≤ (2 * θ + 3 * θ ^ 2) * t := by
          have h2a : 0 ≤ 2 * θ + 3 * θ ^ 2 := by nlinarith [hθ0, sq_nonneg θ]
          exact mul_nonneg h2a ht
        nlinarith [ha, hbθ, h1, h2]
      · push_neg at hθ
        have h1 : (θ - 1 / 11) * H < (θ - 1 / 11) * (11 * t * (1 - 3 * θ)) :=
          mul_lt_mul_of_pos_left hHlt (by linarith)
        have h2 : (θ - 1 / 11) * (11 * t * (1 - 3 * θ)) ≤ (2 * θ + 3 * θ ^ 2) * t := by
          have hmul : 0 ≤ t * ((6 * θ - 1) ^ 2) := mul_nonneg ht (sq_nonneg _)
          nlinarith [hmul]
        nlinarith [ha, hbθ, h1, h2]
    exact le_trans (min_le_right _ _) hkey
