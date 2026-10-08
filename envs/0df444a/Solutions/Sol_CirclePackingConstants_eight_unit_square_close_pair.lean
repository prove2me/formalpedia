-- Prove2me | solution 1 for CirclePackingConstants.eight_unit_square_close_pair
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-06T06:40:44.539991+00:00
-- url     : https://prove2.me/submissions/35c7d9de-1c0b-4185-ab12-9888c0aecc15

import Definitions.Def_CirclePackingConstants
import Theorems.Thm_CirclePackingConstants_eight_diamond_four_close
import Theorems.Thm_CirclePackingConstants_eight_four_points_in_diamond

open CirclePackingConstants

theorem solution : ∀ p : Fin 8 → Point, (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) → ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (2 : ℝ) - Real.sqrt 3 := by
  intro p hp
  by_contra h
  push Not at h
  obtain ⟨q, hq, hd⟩ := eight_four_points_in_diamond p hp (fun i j hij => h i j hij)
  obtain ⟨i, j, hij, hle⟩ := eight_diamond_four_close (fun k => p (q k)) hd
  exact absurd (h (q i) (q j) (fun e => hij (hq e))) (not_lt.mpr hle)
