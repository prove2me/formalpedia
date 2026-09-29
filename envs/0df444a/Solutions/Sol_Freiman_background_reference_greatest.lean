-- Prove2me | solution 1 for Freiman.background_reference_greatest
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:29:53.413739+00:00
-- url     : https://prove2.me/submissions/cbe48842-8ba1-43db-8a01-ea71c88e04a2

import Theorems.Thm_Freiman_cfValue_le_of_first_difference
import Theorems.Thm_Freiman_background_reference_first_difference

open Freiman

theorem solution (r : Bool) (b : ℕ → ℕ+)
    (hb : ∀ n : ℕ, (b n : ℕ) ≤ 4)
    (h14 : OneSidedAvoidsBlock b [1,4])
    (ha : BackgroundAllowed (backgroundReferenceState r) b) :
    cfValue b ≤ cfValue (backgroundReference r) := by
  exact cfValue_le_of_first_difference b (backgroundReference r)
    (background_reference_first_difference r b hb h14 ha)

