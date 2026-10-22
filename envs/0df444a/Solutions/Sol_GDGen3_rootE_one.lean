-- Prove2me | solution 1 for GDGen3.rootE_one
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:36:22.264007+00:00
-- url     : https://prove2.me/submissions/91f05d95-5f49-4054-8a79-3b074994f1e4

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) : rootE r 1 = (1 + r) * (1 - r) ^ 2 / r := by
  unfold rootE
  norm_num only [pow_one, Nat.cast_one]
  field_simp
  ring
