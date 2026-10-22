-- Prove2me | solution 2 for GDGen3.adjacent_interpolation_sum
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:40:59.337196+00:00
-- url     : https://prove2.me/submissions/4d7832c4-da7d-4f17-b19d-564f29db9bb0

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_ginner_forward
import Theorems.Thm_GDGen3_ginner_backward

noncomputable section

open Finset

open GDGen3

theorem solution (h : ℝ) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ)
    (hP : ∀ i j, P i j = P j i) (i : ℕ) :
    2 * (Qv h f P i (i + 1) + Qv h f P (i + 1) i) =
      h * (P i i - P (i + 1) (i + 1))
        - (2 - h) * (P i i + P (i + 1) (i + 1) - 2 * P i (i + 1)) := by
  unfold Qv
  rw [ginner_forward, ginner_backward, hP (i + 1) i]
  ring
