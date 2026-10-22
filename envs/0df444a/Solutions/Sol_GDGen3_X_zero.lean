-- Prove2me | solution 1 for GDGen3.X_zero
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:26:35.968786+00:00
-- url     : https://prove2.me/submissions/c6c2c488-4095-41a8-ab21-2fb708fb399c

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N : ℕ) : X r N 0 = 0 := by
  simp [X, PiS]
