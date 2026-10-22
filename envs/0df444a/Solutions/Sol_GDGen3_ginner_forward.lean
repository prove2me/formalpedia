-- Prove2me | solution 1 for GDGen3.ginner_forward
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:44:39.107907+00:00
-- url     : https://prove2.me/submissions/eb49de21-c829-4667-a84f-42a8294f450a

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (h : ℝ) (P : ℕ → ℕ → ℝ) (i : ℕ) : ginner h P i (i + 1) = h * P (i + 1) i := by
  unfold ginner
  rw [sum_range_succ]
  ring
