-- Prove2me | solution 1 for Freiman.gap_seed_centre
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-10T12:48:13.757342+00:00
-- url     : https://prove2.me/submissions/1f8ee7e6-c700-43f7-97b6-11de8d8c8a92

import Definitions.Def_Freiman_gapModel

open Freiman

theorem solution (a : ℤ → ℕ+) (hs : gapMatch a 0 gapSeedA ∨ gapMatch a 0 gapSeedB) :
    localValue a 0 = 4 + cfValue (gapLeftTail a) + cfValue (gapRightTail a) := by
  -- both seeds carry the digit 4 at their marked centre
  have ha0 : a 0 = (4 : ℕ+) := by
    rcases hs with h | h
    · have h9 := h.2 9 (by decide)
      simpa [gapSeedA] using h9
    · have h5 := h.2 5 (by decide)
      simpa [gapSeedB] using h5
  have hl : (fun n : ℕ => a (0 - (n : ℤ) - 1)) = gapLeftTail a := by
    funext n; unfold gapLeftTail; ring_nf
  have hr : (fun n : ℕ => a (0 + (n : ℤ) + 1)) = gapRightTail a := by
    funext n; unfold gapRightTail; ring_nf
  unfold localValue
  rw [hl, hr, ha0]
  norm_num
