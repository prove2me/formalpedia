-- Prove2me | solution 1 for GDGen3.rootXi_zero
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:29:25.758141+00:00
-- url     : https://prove2.me/submissions/a3a4c8cf-2deb-4bcd-a1eb-7a81086a6fb2

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N : ℕ) : rootXi r N 0 = 0 := by
  simp [rootXi]
