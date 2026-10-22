-- Prove2me | solution 2 for GDGen3.X_zero
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:27:47.358361+00:00
-- url     : https://prove2.me/submissions/97a151af-4ac8-4acc-8a0e-0e6a663e0ad3

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N : ℕ) : X r N 0 = 0 := by
  simp [X, PiS]
