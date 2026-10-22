-- Prove2me | solution 1 for GDGen3.Abar_root_recur
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:39:48.959209+00:00
-- url     : https://prove2.me/submissions/891c6f71-4fb0-43f3-b672-ec032fe29fc6

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N i : ℕ) (hi : 1 ≤ i) :
    Abar (rootXi r N) i = Abar (rootXi r N) (i - 1) *
      (1 + rootXi r N (i - 1)) / rootXi r N i := by
  have he : i - 1 + 1 = i := Nat.sub_add_cancel hi
  conv_lhs => rw [← he]
  rw [Abar, he]
