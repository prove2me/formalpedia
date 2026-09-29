-- Prove2me | solution 1 for CirclePackingConstants.thirty_six_unit_square_close_pair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T09:38:29.262238+00:00
-- url     : https://prove2.me/submissions/46307ad7-224e-43f8-9d84-e8080c738b64
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CirclePackingConstants
import Theorems.Thm_CirclePackingConstants_thirty_six_translate_to_left_bottom
import Theorems.Thm_CirclePackingConstants_thirty_six_left_bottom_close_pair

theorem solution :
    ∀ p : Fin 36 → CirclePackingConstants.Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
      ∃ i j, i ≠ j ∧
        CirclePackingConstants.sqDist (p i) (p j) ≤ (1 : ℝ) / 25 := by
  intro p hp
  obtain ⟨q, hq, hdist, hleft, hbottom⟩ :=
    CirclePackingConstants.thirty_six_translate_to_left_bottom p hp
  obtain ⟨i, j, hij, hclose⟩ :=
    CirclePackingConstants.thirty_six_left_bottom_close_pair q hq hleft hbottom
  refine ⟨i, j, hij, ?_⟩
  calc
    CirclePackingConstants.sqDist (p i) (p j) =
        CirclePackingConstants.sqDist (q i) (q j) := (hdist i j).symm
    _ ≤ (1 : ℝ) / 25 := hclose
