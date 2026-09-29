-- Prove2me | solution 1 for Freiman.background_unrestricted
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:30:05.01096+00:00
-- url     : https://prove2.me/submissions/ad48d251-c19c-4608-935a-4015ce061dea

import Theorems.Thm_Freiman_background_unrestricted_tail

open Freiman

theorem solution (a : ℤ → ℕ+) (ha : ∀ i : ℤ, (a i : ℕ) ≤ 3) (i : ℤ) :
    localValue a i ≤ Real.sqrt 21 := by
  have hl := background_unrestricted_tail (fun n : ℕ => a (i - (n : ℤ) - 1))
    (fun n => ha (i - (n : ℤ) - 1))
  have hr := background_unrestricted_tail (fun n : ℕ => a (i + (n : ℤ) + 1))
    (fun n => ha (i + (n : ℤ) + 1))
  have hi : ((a i : ℕ) : ℝ) ≤ 3 := by exact_mod_cast ha i
  unfold localValue
  linarith

