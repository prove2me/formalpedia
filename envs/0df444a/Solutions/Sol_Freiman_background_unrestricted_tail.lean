-- Prove2me | solution 1 for Freiman.background_unrestricted_tail
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:30:05.301325+00:00
-- url     : https://prove2.me/submissions/412d7adb-ec56-45e8-84f3-41135046b024

import Theorems.Thm_Freiman_cfValue_le_of_first_difference
import Theorems.Thm_Freiman_background_period13_first_difference
import Theorems.Thm_Freiman_background_period13_value

open Freiman

theorem solution (b : ℕ → ℕ+) (hb : ∀ n : ℕ, (b n : ℕ) ≤ 3) :
    cfValue b ≤ (Real.sqrt 21 - 3) / 2 := by
  have hle : cfValue b ≤ cfValue backgroundPeriod13 :=
    cfValue_le_of_first_difference b backgroundPeriod13
      (background_period13_first_difference b hb)
  simpa only [background_period13_value] using hle

