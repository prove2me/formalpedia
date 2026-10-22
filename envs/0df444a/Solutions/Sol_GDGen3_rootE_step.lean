-- Prove2me | solution 1 for GDGen3.rootE_step
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:36:39.432929+00:00
-- url     : https://prove2.me/submissions/0d708f3f-6389-4e25-a545-6cf96ad0d521

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (i : ℕ) :
    rootE r (i + 1) - rootE r i = (1 + r) * (1 - r) * (1 / r ^ (i + 1) - 1) := by
  unfold rootE
  push_cast
  rw [pow_succ r i]
  field_simp
  ring
