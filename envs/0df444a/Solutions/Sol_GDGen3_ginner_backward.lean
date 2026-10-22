-- Prove2me | solution 1 for GDGen3.ginner_backward
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:44:40.295848+00:00
-- url     : https://prove2.me/submissions/5c97d364-5fa3-4756-a501-27f638f0e30e

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (h : ℝ) (P : ℕ → ℕ → ℝ) (i : ℕ) : ginner h P (i + 1) i = -h * P i i := by
  unfold ginner
  rw [sum_range_succ]
  ring
